#include <caml/mlvalues.h>
#include <caml/alloc.h>

#ifdef CAMLprim
#undef CAMLprim
#endif

#define CAMLprim __attribute__((used))
#define STUB { /* __wasi_trace("coq:perf stub"); */ return Atom(0); }

/* perf.c */
CAMLprim value CAML_init(value unit) STUB
CAMLprim value CAML_drop(value unit) STUB
CAMLprim value CAML_peek(value unit) STUB
