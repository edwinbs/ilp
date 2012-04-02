#include "dr_api.h"

#include <map>
#include <set>

using namespace std;


static void *stats_mutex; /* for multithread support */
static int num_bb;
static double ave_size;
static int max_size;

static void event_exit(void);
static dr_emit_flags_t event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                                         bool for_trace, bool translating);

DR_EXPORT void 
dr_init(client_id_t id)
{
    num_bb = 0;
    ave_size = 0.;
    max_size = 0;
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
                      "Number of basic blocks seen: %d\n"
                      "               Maximum size: %d instructions\n"
                      "               Average size: %5.1f instructions\n",
                      num_bb, max_size, ave_size);
    DR_ASSERT(len > 0);
    msg[sizeof(msg)/sizeof(msg[0])-1] = '\0';
    printf("%s", msg);
    dr_mutex_destroy(stats_mutex);
}

#define _MAX(x, y) (((x) > (y)) ? (x) : (y))

static dr_emit_flags_t
event_basic_block(void *drcontext, void *tag, instrlist_t *bb,
                  bool for_trace, bool translating)
{
    int ni = 0;
    int nc = 0;
    
    map<reg_id_t, int>  reg_nc;

    /* we use fp ops so we have to save fp state */
    byte fp_raw[512 + 16];
    byte *fp_align = (byte *) ( (((ptr_uint_t)fp_raw) + 16) & ((ptr_uint_t)-16) );

    if (translating)
        return DR_EMIT_DEFAULT;

    proc_save_fpstate(fp_align);

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

    double ilp = 0.0;
    if (nc > 0)
        ilp = ((double) ni) / nc;
    else /* no dependencies, all can execute in parallel */
        ilp = ni;
        
    DR_ASSERT(ilp >= 1.0);

    dr_mutex_lock(stats_mutex);
    dr_fprintf(STDERR, "ni=%d, nc=%d, ilp=%2.3f\n", ni, nc, ilp);
    /*
    dr_fprintf(STDERR,
	       "Average: cur=%d, old=%8.1f, num=%d, old*num=%8.1f\n"
	       "\told*num+cur=%8.1f, new=%8.1f\n",
	       ni, ave_size, num_bb, ave_size*num_bb,
	       (ave_size * num_bb) + ni,
	       ((ave_size * num_bb) + ni) / (double) (num_bb+1));
	       */

    if (ni > max_size)
	max_size = ni;
    ave_size = ((ave_size * num_bb) + ni) / (double) (num_bb+1);
    num_bb++;
    dr_mutex_unlock(stats_mutex);

    proc_restore_fpstate(fp_align);

    return DR_EMIT_DEFAULT;
}
