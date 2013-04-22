#include "dr_api.h"

#include <stdint.h>
#include <map>
#include <set>
#include <utility>
#include <vector>

#define USE_CLEAN_CALLS
//#define THREAD_SAFE_CLEAN_CALLS
#define FIND_DEAD_EFLAGS

using namespace std;

typedef struct {
    uint64_t total_ni;
    uint64_t sum_ilp;
} ilp_stats;

static ilp_stats stats;
static ilp_stats offline_stats;

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

    offline_stats.total_ni = 0;
    offline_stats.sum_ilp = 0;
    
#ifdef THREAD_SAFE_CLEAN_CALLS
    stats_mutex = dr_mutex_create();
#endif
    
    dr_register_bb_event(event_basic_block);
    dr_register_exit_event(event_exit);
}

static void 
event_exit(void)
{
    fprintf(stderr, "ilp=%.4f\n",
        (double) stats.sum_ilp / stats.total_ni / 1000);

    fprintf(stderr, "ilp-offline=%.4f\n",
        (double) offline_stats.sum_ilp / offline_stats.total_ni / 1000);
        
#ifdef THREAD_SAFE_CLEAN_CALLS
    dr_mutex_destroy(stats_mutex);
#endif
}

inline reg_id_t
get_full_size_reg(reg_id_t reg)
{
    switch (reg)
    {
    case DR_REG_EAX: case DR_REG_AX: case DR_REG_AH: case DR_REG_AL: return DR_REG_EAX;
    case DR_REG_ECX: case DR_REG_CX: case DR_REG_CH: case DR_REG_CL: return DR_REG_ECX;
    case DR_REG_EDX: case DR_REG_DX: case DR_REG_DH: case DR_REG_DL: return DR_REG_EDX;
    case DR_REG_EBX: case DR_REG_BX: case DR_REG_BH: case DR_REG_BL: return DR_REG_EBX;
    }
    return reg;
}

inline void
insert_unique(vector<opnd_t>& list, const opnd_t& opnd)
{
    for (vector<opnd_t>::const_iterator it = list.begin();
         it != list.end(); ++it)
    {
        if (opnd_same_address(opnd, *it))
            return;
    }
    list.push_back(opnd);
}

inline pair<opnd_t, int>*
find_same_mem(vector< pair<opnd_t, int> >& list, const opnd_t& opnd)
{
    for (vector< pair<opnd_t, int> >::iterator it = list.begin();
         it != list.end(); ++it)
    {
        if (opnd_same_address(opnd, it->first))
        {
            return &(*it);
        }
    }
    return NULL;
}

inline void
get_read_eflags(uint eflags, set<int>& read_eflags)
{
    if (eflags & EFLAGS_READ_AF) read_eflags.insert(EFLAGS_AF);
    if (eflags & EFLAGS_READ_CF) read_eflags.insert(EFLAGS_CF);
    if (eflags & EFLAGS_READ_DF) read_eflags.insert(EFLAGS_DF);
    if (eflags & EFLAGS_READ_OF) read_eflags.insert(EFLAGS_OF);
    if (eflags & EFLAGS_READ_PF) read_eflags.insert(EFLAGS_PF);
}

inline void
get_write_eflags(uint eflags, set<int>& write_eflags)
{
    if (eflags & EFLAGS_WRITE_AF) write_eflags.insert(EFLAGS_AF);
    if (eflags & EFLAGS_WRITE_CF) write_eflags.insert(EFLAGS_CF);
    if (eflags & EFLAGS_WRITE_DF) write_eflags.insert(EFLAGS_DF);
    if (eflags & EFLAGS_WRITE_OF) write_eflags.insert(EFLAGS_OF);
    if (eflags & EFLAGS_WRITE_PF) write_eflags.insert(EFLAGS_PF);
}

#define _MAX(x, y) (((x) > (y)) ? (x) : (y))

static void
calculate_ilp(instrlist_t* bb, int32_t& ni, int32_t& ilp)
{
    ni = 0;
    int nc = 0;
    map<reg_id_t, int> reg_nc;
    //vector< pair<opnd_t, int> >  mem_nc;
    int mem_nc = 0;
    map<int, int> eflags_nc;

    /* Look for the following types of dependencies:
     *     reg -> reg
     *     reg -> base_reg in base+disp memory
     *     mem -> mem, in opnd_same_mem() we trust
     *     EFLAGS
     */

    for (instr_t* instr = instrlist_first(bb);
         instr != NULL; instr = instr_get_next(instr))
    {
        int ic = 0;
        
        /* Process source operands */
        set<reg_id_t>    src_regs;
        vector<opnd_t>   src_mems;
        set<int>         read_eflags;
        
        int src_cnt = instr_num_srcs(instr);
        for (int i = 0; i < src_cnt; ++i)
        {
            opnd_t opnd = instr_get_src(instr, i);
            if (opnd_is_reg(opnd))
                src_regs.insert(opnd_get_reg(opnd));
            else if (opnd_is_base_disp(opnd))
            {
                src_regs.insert(opnd_get_base(opnd));
                insert_unique(src_mems, opnd);
            }
            else if (opnd_is_abs_addr(opnd) || opnd_is_pc(opnd))
            {
                insert_unique(src_mems, opnd);
            }
        }

        int dst_cnt_1 = instr_num_dsts(instr);
        for (int i = 0; i < dst_cnt_1; ++i)
        {
            opnd_t opnd = instr_get_dst(instr, i);
            if (opnd_is_reg(opnd))
                src_regs.insert(opnd_get_reg(opnd));
            else if (opnd_is_base_disp(opnd))
            {
                src_regs.insert(opnd_get_base(opnd));
                insert_unique(src_mems, opnd);
            }
            else if (opnd_is_abs_addr(opnd) || opnd_is_pc(opnd))
            {
                insert_unique(src_mems, opnd);
            }
        }
        
        uint eflags = instr_get_eflags(instr);
        get_read_eflags(eflags, read_eflags);
        
        for (set<reg_id_t>::const_iterator it = src_regs.begin();
             it != src_regs.end(); ++it)
        {
            ic = _MAX(ic, reg_nc[*it]);
        }
        
        for (vector<opnd_t>::const_iterator it = src_mems.begin();
             it != src_mems.end(); ++it)
        {
            //pair<opnd_t, int>* pRecord = find_same_mem(mem_nc, *it);
            //if (pRecord)
            //    ic = _MAX(ic, pRecord->second);    
            ic = _MAX(ic, mem_nc);    
        }
        
        for (set<int>::const_iterator it = read_eflags.begin();
             it != read_eflags.end(); ++it)
        {
            ic = _MAX(ic, eflags_nc[*it]);
        }
        
        nc = _MAX(ic, nc);
        
        /* Process destination operands */
        set<reg_id_t>    dst_regs;
        vector<opnd_t>   dst_mems;
        set<int>         write_eflags;
        
        int dst_cnt = instr_num_dsts(instr);
        for (int i = 0; i < dst_cnt; ++i)
        {
            opnd_t opnd = instr_get_dst(instr, i);
            if (opnd_is_reg(opnd))
                dst_regs.insert(opnd_get_reg(opnd));
            else if (opnd_is_base_disp(opnd) || opnd_is_abs_addr(opnd))
            {
                insert_unique(dst_mems, opnd);
            }
        }
        
        get_write_eflags(eflags, write_eflags);
        
        for (set<reg_id_t>::const_iterator it = dst_regs.begin();
             it != dst_regs.end(); ++it)
        {
            reg_nc[*it] = ic + 1;
        }
        
        for (vector<opnd_t>::const_iterator it = dst_mems.begin();
             it != dst_mems.end(); ++it)
        {
            //pair<opnd_t, int>* pRecord = find_same_mem(mem_nc, *it);
            //if (pRecord)
            //    pRecord->second = ic + 1;
            //else
            //    mem_nc.push_back(pair<opnd_t, int>(*it, 1));
            mem_nc = ic + 1;
        }
        
        for (set<int>::const_iterator it = write_eflags.begin();
             it != write_eflags.end(); ++it)
        {
            eflags_nc[*it] = ic + 1;
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
    
    //dr_fprintf(STDERR, "BB: size=%d, ILP=%.3f\n", ni, (double) ilp / 1000);
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

    offline_stats.total_ni += num_instr;
    offline_stats.sum_ilp += ilp_sum_offset;
    
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
