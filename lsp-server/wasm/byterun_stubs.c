#include <caml/mlvalues.h>
#include <caml/alloc.h>

#ifdef CAMLprim
#undef CAMLprim
#endif

#define CAMLprim __attribute__((used))
#define STUB { /* __wasi_trace("coq:byterun stub"); */ return Atom(0); }

/* rocq_float64.c */

CAMLprim value rocq_is_double(value x)               STUB

CAMLprim value rocq_feq_byte(value a, value b)       STUB
CAMLprim value rocq_flt_byte(value a, value b)       STUB
CAMLprim value rocq_fgt_byte(value a, value b)       STUB

CAMLprim value rocq_fmul_byte(value a, value b)      STUB
CAMLprim value rocq_fadd_byte(value a, value b)     { return caml_copy_double(Double_val(a) + Double_val(b)); }
CAMLprim value rocq_fsub_byte(value a, value b)      STUB
CAMLprim value rocq_fdiv_byte(value a, value b)      STUB

CAMLprim value rocq_fsqrt_byte(value a)              STUB
CAMLprim value rocq_next_up_byte(value a)            STUB
CAMLprim value rocq_next_down_byte(value a)          STUB

/* rocq_fix_code.h */
CAMLprim value rocq_accumulate(value unit)           STUB
CAMLprim value rocq_tcode_of_code(value code)        STUB
CAMLprim value rocq_makeaccu (value i)               STUB
CAMLprim value rocq_pushpop (value i)                STUB
CAMLprim value rocq_accucond (value i)               STUB
CAMLprim value rocq_is_accumulate_code(value code)   STUB

/* for 63 bits */
CAMLprim value rocq_uint63_to_float_byte(value i)    STUB

/* rocq_interp.h */

CAMLprim value rocq_push_ra(value tcode)                                   STUB
CAMLprim value rocq_push_val(value v)                                      STUB
CAMLprim value rocq_push_arguments(value args)                             STUB
CAMLprim value rocq_push_vstack(value stk)                                 STUB
CAMLprim value rocq_interprete_ml(value tcode, value a, value t,
                                 value g, value e, value ea)               STUB
CAMLprim value rocq_interprete_byte(value* argv, int argn)                 STUB
CAMLprim value rocq_interprete(code_t rocq_pc, value rocq_accu,
            value rocq_atom_tbl, value rocq_global_data,
            value rocq_env, long rocq_extra_args)                          STUB
CAMLprim value rocq_eval_tcode (value tcode, value t, value g, value e)    STUB

/* rocq_memory.h */

CAMLprim value rocq_static_alloc(value size)         STUB
CAMLprim value init_rocq_vm(value unit)              STUB
CAMLprim value re_init_rocq_vm(value unit)           STUB
CAMLprim value rocq_set_transp_value(value transp)   STUB
CAMLprim value get_rocq_transp_value(value unit)     STUB

CAMLprim value rocq_set_drawinstr(value unit)        STUB

/* rocq_memory.c */

CAMLprim value accumulate_code(value unit)          STUB

/* rocq_values.c */

CAMLprim value rocq_kind_of_closure(value v)                            STUB
CAMLprim value rocq_closure_arity(value clos)                           STUB
CAMLprim value rocq_current_fix(value v)                                STUB
CAMLprim value rocq_shift_fix(value v, value offset)                    STUB
CAMLprim value rocq_last_fix(value v)                                   STUB
CAMLprim value rocq_set_bytecode_field(value v, value i, value code)    STUB
CAMLprim value rocq_offset_tcode(value code, value offset)              STUB
CAMLprim value rocq_int_tcode(value pc, value offset)                   STUB
CAMLprim value rocq_tcode_array(value tcodes)                           STUB
CAMLprim value rocq_obj_set_tag (value arg, value new_tag)              STUB
