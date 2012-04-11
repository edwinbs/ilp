#include "dr_api.h"

#include <stdint.h>
#include <utility>
#include <vector>

//#define USE_CLEAN_CALLS
//#define THREAD_SAFE_CLEAN_CALLS
//#define FIND_DEAD_EFLAGS

using namespace std;

typedef struct {
    uint64_t total_ni;
    uint64_t sum_ilp;
} ilp_stats;

static ilp_stats stats;

#ifdef THREAD_SAFE_CLEAN_CALLS
static void* stats_mutex;
#endif

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag,
    instrlist_t *bb, bool for_trace, bool translating);

DR_EXPORT void 
dr_init(client_id_t id)
{
    stats.total_ni = 0;
    stats.sum_ilp = 0;
    
#ifdef THREAD_SAFE_CLEAN_CALLS
    stats_mutex = dr_mutex_create();
#endif
    
    dr_register_bb_event(event_basic_block);
    dr_register_exit_event(event_exit);
}

static void 
event_exit(void)
{
    printf("Average instruction level parallelism: %.3f\n",
        (double) stats.sum_ilp / stats.total_ni / 1000);
        
#ifdef THREAD_SAFE_CLEAN_CALLS
    dr_mutex_destroy(stats_mutex);
#endif
}

void insert_if_unique(vector<opnd_t>& vecOpnds, const opnd_t& opnd)
{
    for (vector<opnd_t>::const_iterator it = vecOpnds.begin();
         it != vecOpnds.end(); ++it)
    {
        if (opnd_share_reg(*it, opnd))
            return;
    }
    vecOpnds.push_back(opnd);
}

pair<opnd_t, int> *get_match_by_reg(vector< pair<opnd_t, int> >& vecPairs, const opnd_t& opnd)
{
    for (vector< pair<opnd_t, int> >::iterator it = vecPairs.begin();
         it != vecPairs.end(); ++it)
    {
        if (opnd_share_reg(it->first, opnd))
        {
            return &(*it);
        }
    }
    return NULL;
}

void get_unique_src_opnds(vector<opnd_t>& vecUniqueOpnds, instr_t* instr)
{
    int src_opnds = instr_num_srcs(instr);
    for (int i = 0; i < src_opnds; ++i)
    {
        insert_if_unique(vecUniqueOpnds, instr_get_src(instr, i));
    }
}

void get_unique_dst_opnds(vector<opnd_t>& vecUniqueOpnds, instr_t* instr)
{
    int dst_opnds = instr_num_dsts(instr);
    for (int i = 0; i < dst_opnds; ++i)
    {
        opnd_t opnd = instr_get_dst(instr, i);
        if (!opnd_is_reg(opnd)) continue;
        insert_if_unique(vecUniqueOpnds, opnd);
    }
}

#define _MAX(x, y) (((x) > (y)) ? (x) : (y))

static void
calculate_ilp(instrlist_t* bb, int32_t& ni, int32_t& ilp)
{
    ni = 0;
    int nc = 0;
    vector< pair<opnd_t, int> > opnd_nc;

    /* Look for the following types of dependencies:
     *     reg -> reg
     *     reg -> base_reg in base+disp memory
     *     mem -> mem (base+disp), same base and disp
     */

    for (instr_t* instr = instrlist_first(bb);
         instr != NULL; instr = instr_get_next(instr))
    {
        int ic = 0;
        
        /* Process source operands */
        vector<opnd_t> unique_srcs;
        get_unique_src_opnds(unique_srcs, instr);
        
        for (vector<opnd_t>::const_iterator it = unique_srcs.begin();
             it != unique_srcs.end(); ++it)
        {
            pair<opnd_t, int> *pMatch = get_match_by_reg(opnd_nc, *it);
            if (pMatch)
                ic = _MAX(ic, pMatch->second);
        }
        
        nc = _MAX(ic, nc);
        
        /* Process destination operands */
        vector<opnd_t> unique_dsts;
        get_unique_dst_opnds(unique_dsts, instr);
        
        for (vector<opnd_t>::const_iterator it = unique_dsts.begin();
             it != unique_dsts.end(); ++it)
        {
            pair<opnd_t, int> *pMatch = get_match_by_reg(opnd_nc, *it);
            if (pMatch)
                pMatch->second = ic + 1;
            else
                opnd_nc.push_back(pair<opnd_t, int>(*it, 1));
        }
        
        /* Increment the instruction count */
	    ni++;
	}
	
    if (nc > 0)
        ilp =  (ni * 1000) / nc;
    else /* no dependencies, all can execute in parallel */
        ilp = (ni * 1000);
        
    if (ilp < 1000)
    {
        dr_fprintf(STDERR, "Assertion FAILED: ilp=%d\n", ilp);
        throw -1;
    }
    
    dr_fprintf(STDERR, "BB: size=%d, ILP=%.3f\n", ni, (double) ilp / 1000);
}

#define TESTALL(mask, var) (((mask) & (var)) == (mask))

#define TESTANY(mask, var) (((mask) & (var)) != 0)

#define EFLAGS_DEAD(x) (TESTALL(EFLAGS_WRITE_6, (x)) \
    && !TESTANY(EFLAGS_READ_6, (x)))

static bool
find_dead_eflags_instr(instrlist_t *bb, instr_t* pos)
{
    for (instr_t* ins = instrlist_first(bb);
         ins != NULL; ins = instr_get_next(ins))
    {
        unsigned int flags = instr_get_arith_flags(ins);
        if (EFLAGS_DEAD(flags))
        {
            pos = ins;
            return true;
        }
    }
    pos = instrlist_first(bb);
    return false;
}

inline static void
preinsert_add64(void* dc, instrlist_t* bb, instr_t* pos,
                void* absmem, int32_t addend)
{
    instrlist_meta_preinsert(bb, pos,
        LOCK(INSTR_CREATE_add(dc,
        OPND_CREATE_ABSMEM((byte *)absmem, OPSZ_4),
        OPND_CREATE_INT32(addend))));
      
    instrlist_meta_preinsert(bb, pos,
        LOCK(INSTR_CREATE_adc(dc,
        OPND_CREATE_ABSMEM((byte *)absmem + 4, OPSZ_4),
        OPND_CREATE_INT8(0))));
}

static void
update_ilp(int32_t ni, int32_t sum_offset)
{
#ifdef THREAD_SAFE_CLEAN_CALLS
    dr_mutex_lock(stats_mutex);
#endif

    stats.total_ni += ni;
    stats.sum_ilp += sum_offset;
    
#ifdef THREAD_SAFE_CLEAN_CALLS
    dr_mutex_unlock(stats_mutex);
#endif
}

static dr_emit_flags_t
event_basic_block(void *dc, void *tag, instrlist_t *bb,
                  bool for_trace, bool translating)
{
    int32_t num_instr = 0;
    int32_t ilp = 0;
    int32_t ilp_sum_offset = 0;
    
    calculate_ilp(bb, num_instr, ilp);
    ilp_sum_offset = ilp * num_instr;
    
    instr_t* pos = instrlist_first(bb);

#ifdef USE_CLEAN_CALLS
    dr_insert_clean_call(dc, bb, pos, (void*) update_ilp, false, 2,
                         OPND_CREATE_INT32(num_instr),
                         OPND_CREATE_INT32(ilp_sum_offset));
#else
#ifdef FIND_DEAD_EFLAGS
    bool dead_eflags_found = find_dead_eflags_instr(bb, pos);
   
    if (!dead_eflags_found)
#endif
        dr_save_arith_flags(dc, bb, pos, SPILL_SLOT_1);

    preinsert_add64(dc, bb, pos, &stats.total_ni, num_instr);
    preinsert_add64(dc, bb, pos, &stats.sum_ilp, ilp_sum_offset);    

#ifdef FIND_DEAD_EFLAGS
    if (!dead_eflags_found)
#endif
        dr_restore_arith_flags(dc, bb, pos, SPILL_SLOT_1);
#endif
    
    return DR_EMIT_DEFAULT;
}
