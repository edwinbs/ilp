#include "dr_api.h"

#include <stdint.h>
#include <map>
#include <set>
#include <utility>
#include <vector>

using namespace std;


static void *stats_mutex; /* for multithread support */

static int64_t total_ni;
static int64_t sum_ilp;

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                                         bool for_trace, bool translating);

DR_EXPORT void 
dr_init(client_id_t id)
{
    total_ni = 0;
    sum_ilp = 0;
    stats_mutex = dr_mutex_create();
    dr_register_bb_event(event_basic_block);
    dr_register_exit_event(event_exit);
}

static void 
event_exit(void)
{
    char msg[512];
    int len;
    double avg_ilp = sum_ilp / total_ni;
    len = dr_snprintf(msg, sizeof(msg)/sizeof(msg[0]),
                      "Average instruction level parallelism: %.3f\n"
                      "                   Instructions count: %u\n",
                      avg_ilp / 1000, total_ni);
    DR_ASSERT(len > 0);
    msg[sizeof(msg)/sizeof(msg[0])-1] = '\0';
    printf("%s", msg);
    
    dr_mutex_destroy(stats_mutex);
}

static void
update_avg_ilp(int32_t bb_ilp, int32_t bb_size)
{
    //dr_mutex_lock(stats_mutex);
    
    total_ni += bb_size;
    sum_ilp += bb_ilp * bb_size;
    
    //dr_mutex_unlock(stats_mutex);
}

#define _MAX(x, y) (((x) > (y)) ? (x) : (y))

static dr_emit_flags_t
event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                  bool for_trace, bool translating)
{
    int ni = 0;
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
        vector<opnd_t> unique_opnds;
        
        /* Process source operands */
        int src_opnds = instr_num_srcs(instr);
        for (int i = 0; i < src_opnds; ++i)
        {   
            opnd_t opnd = instr_get_src(instr, i);
            
            vector<opnd_t>::const_iterator it1;
            for (it1 = unique_opnds.begin(); it1 != unique_opnds.end(); ++it1)
            {
                if (opnd_share_reg(*it1, opnd))
                    break;
            }
            
            if (it1 == unique_opnds.end())
                unique_opnds.push_back(opnd);
        }
        
        for (vector<opnd_t>::const_iterator it1 = unique_opnds.begin();
             it1 != unique_opnds.end(); ++it1)
        {
            vector< pair<opnd_t, int> >::const_iterator it2;
            for (it2 = opnd_nc.begin(); it2 != opnd_nc.end(); ++it2)
            {
                if (opnd_share_reg(it2->first, *it1))
                {
                    nc = _MAX(nc, it2->second);
                    break;
                }
            }
        }
        
        unique_opnds.clear();
        
        /* Process destination operands */
        int dst_opnds = instr_num_dsts(instr);
        for (int i = 0; i < dst_opnds; ++i)
        {
            opnd_t opnd = instr_get_dst(instr, i);
            
            if (!opnd_is_reg(opnd))
                continue;
            
            vector<opnd_t>::const_iterator it1;
            for (it1 = unique_opnds.begin(); it1 != unique_opnds.end(); ++it1)
            {
                if (opnd_share_reg(*it1, opnd))
                    break;
            }
            
            if (it1 == unique_opnds.end())
                unique_opnds.push_back(opnd);
        }
        
        for (vector<opnd_t>::const_iterator it1 = unique_opnds.begin();
             it1 != unique_opnds.end(); ++it1)
        {
            vector< pair<opnd_t, int> >::iterator it2;
            for (it2 = opnd_nc.begin(); it2 != opnd_nc.end(); ++it2)
            {
                if (opnd_share_reg(it2->first, *it1))
                {
                    ++(it2->second);
                    nc = _MAX(nc, it2->second);
                    break;
                }
            }
            if (it2 == opnd_nc.end())
                opnd_nc.push_back(pair<opnd_t, int>(*it1, 1));
        }
        
        /* Number of instructions */
	    ni++;
	}

    int ilp = 0;
    if (nc > 0)
        ilp =  (ni * 1000) / nc;
    else /* no dependencies, all can execute in parallel */
        ilp = (ni * 1000);
        
    if (ilp < 1000)
    {
        dr_fprintf(STDERR, "Assertion FAILED: ilp=%d\n", ilp);
        throw -1;
    }
    
    instr_t* first_instr = instrlist_first(bb);
    
    dr_insert_clean_call(drcontext, bb, first_instr,
                         (void*) update_avg_ilp,
                         false, 2,
                         OPND_CREATE_INT32(ilp),
                         OPND_CREATE_INT32(ni));
    
    return DR_EMIT_DEFAULT;
}
