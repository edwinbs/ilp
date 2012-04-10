#include "dr_api.h"

#include <stdint.h>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace std;

static void *stats_mutex; /* for multithread support */

typedef struct {
    uint64_t total_ni;
    uint64_t sum_ilp;
} ilp_stats;

static ilp_stats stats;

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag,
    instrlist_t *bb, bool for_trace, bool translating);

DR_EXPORT void 
dr_init(client_id_t id)
{
    stats.total_ni = 0;
    stats.sum_ilp = 0;
    stats_mutex = dr_mutex_create();
    dr_register_bb_event(event_basic_block);
    dr_register_exit_event(event_exit);
}

static void 
event_exit(void)
{
    char msg[512];
    int len;
    double avg_ilp = stats.sum_ilp / stats.total_ni;
    len = dr_snprintf(msg, sizeof(msg)/sizeof(msg[0]),
                      "Average instruction level parallelism: %.3f\n"
                      "                   Instructions count: %u\n",
                      avg_ilp / 1000, stats.total_ni);
    DR_ASSERT(len > 0);
    msg[sizeof(msg)/sizeof(msg[0])-1] = '\0';
    printf("%s", msg);
    
    dr_mutex_destroy(stats_mutex);
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
        /* Process source operands */
        vector<opnd_t> unique_srcs;
        get_unique_src_opnds(unique_srcs, instr);
        
        for (vector<opnd_t>::const_iterator it = unique_srcs.begin();
             it != unique_srcs.end(); ++it)
        {
            pair<opnd_t, int> *pMatch = get_match_by_reg(opnd_nc, *it);
            if (pMatch)
                nc = _MAX(nc, pMatch->second);
        }
        
        /* Process destination operands */
        vector<opnd_t> unique_dsts;
        get_unique_dst_opnds(unique_dsts, instr);
        
        for (vector<opnd_t>::const_iterator it = unique_dsts.begin();
             it != unique_dsts.end(); ++it)
        {
            pair<opnd_t, int> *pMatch = get_match_by_reg(opnd_nc, *it);
            if (pMatch)
            {
                ++(pMatch->second);
                nc = _MAX(nc, pMatch->second);
            }
            else
            {
                opnd_nc.push_back(pair<opnd_t, int>(*it, 1));
            }
        }
        
        /* Number of instructions */
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
}

#define TESTALL(mask, var) (((mask) & (var)) == (mask))

#define TESTANY(mask, var) (((mask) & (var)) != 0)

#define EFLAGS_DEAD(x) (TESTALL(EFLAGS_WRITE_6, (x)) \
    && !TESTANY(EFLAGS_READ_6, (x)))

static dr_emit_flags_t
event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                  bool for_trace, bool translating)
{
    int32_t num_instr = 0;
    int32_t ilp = 0;
    
    calculate_ilp(bb, num_instr, ilp);
    
    bool eflags_save_needed = true;
    instr_t* where = instrlist_first(bb);
    for (instr_t* ins = instrlist_first(bb);
         ins != NULL; ins = instr_get_next(ins))
    {
        unsigned int flags = instr_get_arith_flags(ins);
        if (EFLAGS_DEAD(flags))
        {
            where = ins;
            eflags_save_needed = false;
        }
    }
    
    if (eflags_save_needed)
        dr_save_arith_flags(drcontext, bb, where, SPILL_SLOT_1);
                         
    instrlist_meta_preinsert(bb, where,
        LOCK(INSTR_CREATE_add(drcontext,
        OPND_CREATE_ABSMEM((byte *)&stats.total_ni, OPSZ_4),
        OPND_CREATE_INT32(num_instr))));
      
    instrlist_meta_preinsert(bb, where,
        LOCK(INSTR_CREATE_adc(drcontext,
        OPND_CREATE_ABSMEM((byte *)&stats.total_ni + 4, OPSZ_4),
        OPND_CREATE_INT8(0))));
        
    instrlist_meta_preinsert(bb, where,
        LOCK(INSTR_CREATE_add(drcontext,
        OPND_CREATE_ABSMEM((byte *)&stats.sum_ilp, OPSZ_4),
        OPND_CREATE_INT32(ilp * num_instr))));
        
    instrlist_meta_preinsert(bb, where,
        LOCK(INSTR_CREATE_adc(drcontext,
        OPND_CREATE_ABSMEM((byte *)&stats.sum_ilp + 4, OPSZ_4),
        OPND_CREATE_INT8(0))));
 
    if (eflags_save_needed)    
        dr_restore_arith_flags(drcontext, bb, where, SPILL_SLOT_1);
    
    return DR_EMIT_DEFAULT;
}
