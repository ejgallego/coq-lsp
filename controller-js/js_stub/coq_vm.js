// Provides: vm_ll
function vm_ll(s, args) { 
  if (vm_ll.log) joo_global_object.console.warn(s, args); 
  if (vm_ll.trap) throw new Error("vm trap: '"+ s + "' not implemented");
}

vm_ll.log = false;     // whether to log calls
vm_ll.trap = false;    // whether to halt on calls

// Provides: init_rocq_vm
// Requires: vm_ll
function init_rocq_vm() {
  vm_ll('init_rocq_vm', arguments);
  return;
}

// EG: Coq VM's code is evil and performs static initialization... the
// best option would be to disable the VM code entirely as before.

// Provides: rocq_vm_trap
// Requires: vm_ll
function rocq_vm_trap() {    // will cause future calls to vm code to fault
  vm_ll.log = vm_ll.trap = true;  // (called after initialization)
}

// Provides: accumulate_code
// Requires: vm_ll
function accumulate_code() {
  // EG: Where the hell is that called from
  vm_ll('accumulate_code', arguments);
  return [];
}

// Provides: rocq_pushpop
// Requires: vm_ll
function rocq_pushpop() {
  vm_ll('rocq_pushpop', arguments);
  return [];
}

// Provides: rocq_closure_arity
// Requires: vm_ll
function rocq_closure_arity() {
  vm_ll('rocq_closure_arity', arguments);
  return [];
}

// Provides: rocq_eval_tcode
// Requires: vm_ll
function rocq_eval_tcode() {
  vm_ll('rocq_eval_tcode', arguments);
  return [];
}

// Provides: rocq_int_tcode
// Requires: vm_ll
function rocq_int_tcode() {
  vm_ll('rocq_int_tcode', arguments);
  return [];
}

// Provides: rocq_interprete_ml
// Requires: vm_ll
function rocq_interprete_ml() {
  vm_ll('rocq_interprete_ml', arguments);
  return [];
}

// Provides: rocq_is_accumulate_code
// Requires: vm_ll
function rocq_is_accumulate_code() {
  vm_ll('rocq_is_accumulate_code', arguments);
  return [];
}

// Provides: rocq_kind_of_closure
// Requires: vm_ll
function rocq_kind_of_closure() {
  vm_ll('rocq_kind_of_closure', arguments);
  return [];
}

// Provides: rocq_makeaccu
// Requires: vm_ll
function rocq_makeaccu() {
  vm_ll('rocq_makeaccu', arguments);
  return [];
}

// Provides: rocq_offset
// Requires: vm_ll
function rocq_offset() {
  vm_ll('rocq_offset', arguments);
  return [];
}

// Provides: rocq_offset_closure
// Requires: vm_ll
function rocq_offset_closure() {
  vm_ll('rocq_offset_closure', arguments);
  return [];
}

// Provides: rocq_offset_tcode
// Requires: vm_ll
function rocq_offset_tcode() {
  vm_ll('rocq_offset_tcode', arguments);
  return [];
}

// Provides: rocq_push_arguments
// Requires: vm_ll
function rocq_push_arguments() {
  vm_ll('rocq_push_arguments', arguments);
  return [];
}

// Provides: rocq_push_ra
// Requires: vm_ll
function rocq_push_ra() {
  vm_ll('rocq_push_ra', arguments);
  return [];
}

// Provides: rocq_push_val
// Requires: vm_ll
function rocq_push_val() {
  vm_ll('rocq_push_val', arguments);
  return [];
}

// Provides: rocq_push_vstack
// Requires: vm_ll
function rocq_push_vstack() {
  vm_ll('rocq_push_vstack', arguments);
  return [];
}

// Provides: rocq_set_transp_value
// Requires: vm_ll
function rocq_set_transp_value() {
  vm_ll('rocq_set_transp_value', arguments);
  return [];
}

// Provides: rocq_set_bytecode_field
// Requires: vm_ll
function rocq_set_bytecode_field() {
  vm_ll('rocq_set_bytecode_field', arguments);
  return [0];
}

// Provides: rocq_tcode_of_code
// Requires: vm_ll
function rocq_tcode_of_code() {
  vm_ll('rocq_tcode_of_code', arguments);
  return [];
}

// Provides: rocq_accumulate
// Requires: vm_ll
function rocq_accumulate() {
  // This is called on init, so let's be more lenient
  // vm_ll('rocq_accumulate', arguments);
  return [];
}

// Provides: rocq_obj_set_tag
// Requires: vm_ll
function rocq_obj_set_tag() {
  vm_ll('rocq_obj_set_tag', arguments);
  return [];
}

// Provides: rocq_uint63_to_float_byte
// Requires: vm_ll
function rocq_uint63_to_float_byte() {
  // First element of the array is the length!
  vm_ll('rocq_uint63_to_float_byte', arguments);
  return [0];
}

// Provides: get_rocq_atom_tbl
// Requires: vm_ll
function get_rocq_atom_tbl() {
  // First element of the array is the length!
  vm_ll('get_rocq_atom_tbl', arguments);
  return [0];
}

// Provides: get_rocq_global_data
// Requires: vm_ll
function get_rocq_global_data() {
  vm_ll('get_rocq_global_data', arguments);
  return [];
}

// Provides: get_rocq_transp_value
// Requires: vm_ll
function get_rocq_transp_value() {
  vm_ll('get_rocq_transp_value', arguments);
  return [];
}

// Provides: realloc_rocq_atom_tbl
// Requires: vm_ll
function realloc_rocq_atom_tbl() {
  vm_ll('realloc_rocq_atom_tbl', arguments);
  return;
}

// Provides: realloc_rocq_global_data
// Requires: vm_ll
function realloc_rocq_global_data() {
  vm_ll('realloc_rocq_global_data', arguments);
  return;
}

// Provides: rocq_interprete_byte
// Requires: vm_ll
function rocq_interprete_byte()    { vm_ll('rocq_interprete_byte', arguments); }
// Provides: rocq_set_drawinstr
// Requires: vm_ll
function rocq_set_drawinstr()      { vm_ll('rocq_set_drawinstr', arguments); }
// Provides: rocq_tcode_array
// Requires: vm_ll
function rocq_tcode_array()        { vm_ll('rocq_tcode_array', arguments); }

// Provides: rocq_fadd_byte
function rocq_fadd_byte(r1, r2) {
  return r1 + r2;
}

// Provides: rocq_fsub_byte
function rocq_fsub_byte(r1, r2) {
  return r1 - r2;
}

// Provides: rocq_fmul_byte
function rocq_fmul_byte(r1, r2) {
  return r1 * r2;
}

// Provides: rocq_fdiv_byte
function rocq_fdiv_byte(r1, r2) {
  return r1 / r2;
}

// Provides: rocq_fsqrt_byte
// Requires: vm_ll
function rocq_fsqrt_byte() {
  vm_ll('rocq_fsqrt_byte', arguments);
  return;
}

// Provides: rocq_is_double
// Requires: vm_ll
  function rocq_is_double() {
    vm_ll('rocq_is_double', arguments);
  return;
}

// Provides: rocq_next_down_byte
// Requires: vm_ll
  function rocq_next_down_byte() {
    vm_ll('rocq_next_down_byte', arguments);
  return;
}

// Provides: rocq_next_up_byte
// Requires: vm_ll
  function rocq_next_up_byte() {
    vm_ll('rocq_next_up_byte', arguments);
  return;
}

// Provides: rocq_current_fix
// Requires: vm_ll
function rocq_current_fix() {
  vm_ll('rocq_current_fix', arguments);
  return [];
}

// Provides: rocq_last_fix
// Requires: vm_ll
function rocq_last_fix() {
  vm_ll('rocq_last_fix', arguments);
  return [];
}

// Provides: rocq_shift_fix
// Requires: vm_ll
function rocq_shift_fix() {
  vm_ll('rocq_shift_fix', arguments);
  return [];
}
