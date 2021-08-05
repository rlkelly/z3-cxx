#pragma once

extern "C" {
    struct _Z3_config;
    struct _Z3_context;
    struct _Z3_symbol;
    struct _Z3_sort;
    struct _Z3_ast;
    struct _Z3_solver;

    _Z3_config* Z3_mk_config(void);
    void Z3_del_config(_Z3_config* c);
    _Z3_context* Z3_mk_context(_Z3_config *c);
    _Z3_symbol* Z3_mk_string_symbol(_Z3_context *c, char *s);

    _Z3_sort* Z3_mk_int_sort(_Z3_context* c);

    _Z3_ast* Z3_mk_const(_Z3_context* c, _Z3_symbol* s, _Z3_sort* ty);
    _Z3_ast* Z3_mk_gt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);

    _Z3_solver* Z3_mk_simple_solver(_Z3_context* c);
    void Z3_solver_assert(_Z3_context* c, _Z3_solver* s, _Z3_ast* a);
    int Z3_solver_check(_Z3_context* c, _Z3_solver* s);

    void Z3_global_param_reset_all(void);
}
