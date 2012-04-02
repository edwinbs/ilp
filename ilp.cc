#include "dr_api.h"

#include <stdint.h>
#include <map>
#include <set>

using namespace std;


static void *stats_mutex; /* for multithread support */

static int total_ni;
static int avg_ilp; //Average ILP multiplied by 1000

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                                         bool for_trace, bool translating);

DR_EXPORT void 
dr_init(client_id_t id)
{
    total_ni = 0;
    avg_ilp = 0.0;
    stats_mutex = dr_mutex_create();
    dr_register_bb_event(event_basic_block);
    dr_register_exit_event(event_exit);
}

static void 
event_exit(void)
{
    char msg[512];
    int len;
    len = dr_snprintf(msg, sizeof(msg)/sizeof(msg[0]),
                      "Average instruction level parallelism: %.3f\n"
                      "                   Instructions count: %d\n",
                      ((double) avg_ilp / 1000.0), total_ni);
    DR_ASSERT(len > 0);
    msg[sizeof(msg)/sizeof(msg[0])-1] = '\0';
    printf("%s", msg);
    
    dr_mutex_destroy(stats_mutex);
}

static void
update_avg_ilp(int bb_ilp, int bb_size)
{
    //dr_fprintf(STDERR, "update_avg_ilp(), bb_ilp=%d, bb_size=%d\n", bb_ilp, bb_size);
    dr_mutex_lock(stats_mutex);
    
    total_ni += bb_size;
    avg_ilp += (bb_ilp - avg_ilp) / total_ni;
    
    dr_mutex_unlock(stats_mutex);
}

#define _MAX(x, y) (((x) > (y)) ? (x) : (y))

static dr_emit_flags_t
event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                  bool for_trace, bool translating)
{
    int ni = 0;
    int nc = 0;
    
    map<reg_id_t, int>  reg_nc;

    for (instr_t* instr = instrlist_first(bb);
         instr != NULL; instr = instr_get_next(instr))
    {
        set<reg_id_t> used_regs;
        
        /* Process source operands */
        int src_opnds = instr_num_srcs(instr);
        for (int i = 0; i < src_opnds; ++i)
        {
            opnd_t opnd = instr_get_src(instr, i);
            int num_regs_used = opnd_num_regs_used(opnd);
            
            for (int j = 0; j < num_regs_used; ++j)
                used_regs.insert(opnd_get_reg_used(opnd, j));
        }
        
        for (set<reg_id_t>::const_iterator it = used_regs.begin();
             it != used_regs.end(); ++it)
        {
            nc = _MAX(nc, reg_nc[*it]);
        }
        
        used_regs.clear();
        
        /* Process destination operands */
        int dst_opnds = instr_num_dsts(instr);
        for (int i = 0; i < dst_opnds; ++i)
        {
            opnd_t opnd = instr_get_dst(instr, i);
            int num_regs_used = opnd_num_regs_used(opnd);
            
            for (int j = 0; j < num_regs_used; ++j)
                used_regs.insert(opnd_get_reg_used(opnd, j));
        }
        
        for (set<reg_id_t>::const_iterator it = used_regs.begin();
             it != used_regs.end(); ++it)
        {
            ++reg_nc[*it];
            nc = _MAX(nc, reg_nc[*it]);
        }
        
        /* Number of instructions */
	    ni++;
	}

    int ilp = 0;
    if (nc > 0)
        ilp =  (ni * 1000) / nc;
    else /* no dependencies, all can execute in parallel */
        ilp = (ni * 1000);
        
    DR_ASSERT(ilp >= 1000);
    
    //dr_fprintf(STDERR, "ni=%d, nc=%d, ilp=%d\n", ni, nc, ilp);
    
    instr_t* first_instr = instrlist_first(bb);
    
    dr_insert_clean_call(drcontext, bb, first_instr,
                         (void*) update_avg_ilp,
                         false, 2,
                         OPND_CREATE_INT32(ilp),
                         OPND_CREATE_INT32(ni));

    return DR_EMIT_DEFAULT;
}
