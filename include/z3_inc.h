#pragma once

#include <cinttypes>

extern "C" {
    typedef enum
    {
        Z3_UNINTERPRETED_SORT,
        Z3_BOOL_SORT,
        Z3_INT_SORT,
        Z3_REAL_SORT,
        Z3_BV_SORT,
        Z3_ARRAY_SORT,
        Z3_DATATYPE_SORT,
        Z3_RELATION_SORT,
        Z3_FINITE_DOMAIN_SORT,
        Z3_FLOATING_POINT_SORT,
        Z3_ROUNDING_MODE_SORT,
        Z3_SEQ_SORT,
        Z3_RE_SORT,
        Z3_UNKNOWN_SORT = 1000
    } Z3_sort_kind;

    typedef enum
    {
        Z3_OK,
        Z3_SORT_ERROR,
        Z3_IOB,
        Z3_INVALID_ARG,
        Z3_PARSER_ERROR,
        Z3_NO_PARSER,
        Z3_INVALID_PATTERN,
        Z3_MEMOUT_FAIL,
        Z3_FILE_ACCESS_ERROR,
        Z3_INTERNAL_FATAL,
        Z3_INVALID_USAGE,
        Z3_DEC_REF_ERROR,
        Z3_EXCEPTION
    } Z3_error_code;

    typedef enum
    {
        Z3_NUMERAL_AST,
        Z3_APP_AST,
        Z3_VAR_AST,
        Z3_QUANTIFIER_AST,
        Z3_SORT_AST,
        Z3_FUNC_DECL_AST,
        Z3_UNKNOWN_AST = 1000
    } Z3_ast_kind;

    typedef enum
    {
        Z3_L_FALSE = -1,
        Z3_L_UNDEF,
        Z3_L_TRUE
    } Z3_lbool;

    struct _Z3_config;
    struct _Z3_context;
    struct _Z3_sort;
    struct _Z3_ast;
    struct _Z3_model;
    struct _Z3_string;
    struct _Z3_func_decl;
    struct _Z3_symbol;
    struct _Z3_literal;
    struct _Z3_app;
    struct _Z3_pattern;
    struct _Z3_constructor;
    struct _Z3_constructor_list;
    struct _Z3_params;
    struct _Z3_param_descrs;
    struct _Z3_goal;
    struct _Z3_tactic;
    struct _Z3_probe;
    struct _Z3_stats;
    struct _Z3_solver;
    struct _Z3_solver_callback;
    struct _Z3_ast_vector;
    struct _Z3_ast_map;
    struct _Z3_apply_result;
    struct _Z3_func_interp;
    struct _Z3_func_entry;
    struct _Z3_fixedpoint;
    struct _Z3_optimize;
    struct _Z3_rcf_num;
    struct _Z3_probe;

    typedef bool Z3_bool_opt;
    typedef const char * Z3_string;
    typedef char const*  Z3_char_ptr;
    typedef Z3_string * Z3_string_ptr;

    typedef void Z3_error_handler(_Z3_context* c, Z3_error_code e);
    void Z3_set_error_handler(_Z3_context* c, Z3_error_handler h);

    void Z3_global_param_set(_Z3_string* param_id, _Z3_string* param_value);
    Z3_bool_opt Z3_global_param_get(_Z3_string* param_id, Z3_string* param_value);
    void Z3_global_param_reset_all(void);

    _Z3_config* Z3_mk_config(void);
    void Z3_del_config(_Z3_config* c);
    void Z3_set_param_value(_Z3_config* c, const char* param_id, const char* param_value);
    _Z3_context* Z3_mk_context(_Z3_config* c);
    void Z3_del_context(_Z3_context* c);
    _Z3_context* Z3_mk_context_rc(_Z3_config* c);

    void Z3_inc_ref(_Z3_context* c, _Z3_ast* a);
    void Z3_dec_ref(_Z3_context* c, _Z3_ast* a);

    void Z3_update_param_value(_Z3_context* c, _Z3_string* param_id, _Z3_string* param_value);
    void Z3_interrupt(_Z3_context* c);

    _Z3_params* Z3_mk_params(_Z3_context* c);
    void Z3_params_inc_ref(_Z3_context* c, _Z3_params* p);
    void Z3_params_dec_ref(_Z3_context* c, _Z3_params* p);
    void Z3_params_set_bool(_Z3_context* c, _Z3_params* p, _Z3_symbol* k, bool v);
    void Z3_params_set_uint(_Z3_context* c, _Z3_params* p, _Z3_symbol* k, unsigned v);
    void Z3_params_set_double(_Z3_context* c, _Z3_params* p, _Z3_symbol* k, double v);
    void Z3_params_set_symbol(_Z3_context* c, _Z3_params* p, _Z3_symbol* k, _Z3_symbol* v);
    const char* Z3_params_to_string(_Z3_context* c, _Z3_params* p);

    _Z3_sort* Z3_mk_int_sort(_Z3_context* c);

    _Z3_ast* Z3_mk_const(_Z3_context* c, _Z3_symbol* s, _Z3_sort* ty);
    _Z3_ast* Z3_mk_fresh_const(_Z3_context* c, Z3_string prefix, _Z3_sort* ty);
    _Z3_ast* Z3_mk_gt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_numeral(_Z3_context* c, Z3_string numeral, _Z3_sort* ty);
    _Z3_ast* Z3_mk_true(_Z3_context* c);
    _Z3_ast* Z3_mk_false(_Z3_context* c);
    Z3_lbool Z3_get_bool_value(_Z3_context* c, _Z3_ast* a);
    _Z3_ast* Z3_translate(_Z3_context* source, _Z3_ast* a, _Z3_context* target);
    _Z3_ast* Z3_mk_ite(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2, _Z3_ast* t3);
    _Z3_ast* Z3_mk_not(_Z3_context* c, _Z3_ast* a);
    _Z3_ast* Z3_mk_real(_Z3_context* c, int num, int den);
    _Z3_ast* Z3_mk_distinct(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_add(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_sub(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_mul(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_power(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_ast* Z3_mk_is_int(_Z3_context* c, _Z3_ast* t1);
    bool Z3_get_numeral_small(_Z3_context* c, _Z3_ast* a, int64_t* num, int64_t* den);
    _Z3_ast* Z3_mk_mod(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_ast* Z3_mk_rem(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_symbol* Z3_mk_string_symbol(_Z3_context* c, const char* s);
    _Z3_symbol* Z3_mk_int_symbol(_Z3_context* c, int i);

    _Z3_ast* Z3_mk_int2real(_Z3_context* c, _Z3_ast* arg1);
    _Z3_ast* Z3_mk_eq(_Z3_context* c, _Z3_ast* l, _Z3_ast* r);
    _Z3_ast* Z3_mk_lt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_le(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_gt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_ge(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_divides(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_simplify(_Z3_context* c, _Z3_ast* a);
    _Z3_ast* Z3_substitute(_Z3_context* c,
                                _Z3_ast* a,
                                unsigned num_exprs,
                                _Z3_ast* const from[],
                                _Z3_ast* const to[]);

    _Z3_app* Z3_to_app(_Z3_context* c, _Z3_ast* a);
    unsigned Z3_get_app_num_args(_Z3_context* c, _Z3_app* a);
    _Z3_ast* Z3_get_app_arg(_Z3_context* c, _Z3_app* a, unsigned i);

    _Z3_ast* Z3_mk_and(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_or(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_xor(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_unary_minus(_Z3_context* c, _Z3_ast* arg);
    _Z3_ast* Z3_mk_div(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_ast* Z3_mk_implies(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_iff(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_pble(_Z3_context* c, unsigned num_args,
                             _Z3_ast* const args[], int const coeffs[],
                             int k);
    _Z3_ast* Z3_mk_pbge(_Z3_context* c, unsigned num_args,
                             _Z3_ast* const args[], int const coeffs[],
                             int k);
    _Z3_ast* Z3_mk_pbeq(_Z3_context* c, unsigned num_args,
                             _Z3_ast* const args[], int const coeffs[],
                             int k);
    _Z3_ast* Z3_mk_int64(_Z3_context* c, int64_t v, _Z3_sort* ty);
    _Z3_ast* Z3_mk_unsigned_int64(_Z3_context* c, uint64_t v, _Z3_sort* ty);

    _Z3_ast* Z3_mk_exists_const(
            _Z3_context* c,
            unsigned weight,
            unsigned num_bound,
            _Z3_app* const bound[],
            unsigned num_patterns,
            _Z3_pattern* const patterns[],
            _Z3_ast* body
            );

    _Z3_solver* Z3_mk_simple_solver(_Z3_context* c);
    void Z3_solver_assert(_Z3_context* c, _Z3_solver* s, _Z3_ast* a);
    Z3_lbool Z3_solver_check(_Z3_context* c, _Z3_solver* s);

    _Z3_model* Z3_solver_get_model(_Z3_context* c, _Z3_solver* s);
    char* Z3_model_to_string(_Z3_context* c, _Z3_model* m);
    char* Z3_ast_to_string(_Z3_context* c, _Z3_ast* a);
    bool Z3_is_eq_ast(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    unsigned Z3_get_ast_hash(_Z3_context* c, _Z3_ast* a);

    bool Z3_model_eval(_Z3_context* c, _Z3_model* m, _Z3_ast* t, bool model_completion, _Z3_ast ** v);

    bool Z3_get_numeral_int(_Z3_context* c, _Z3_ast* v, int* i);

    Z3_ast_kind Z3_get_ast_kind(_Z3_context* c, _Z3_ast* a);

    void Z3_global_param_reset_all(void);

    _Z3_func_decl* Z3_mk_func_decl(_Z3_context* c, _Z3_symbol* s,
                                    unsigned domain_size, _Z3_sort* const domain[],
                                    _Z3_sort* range);


    _Z3_sort* Z3_get_sort(_Z3_context* c, _Z3_ast* a);
    bool Z3_is_string_sort(_Z3_context* c, _Z3_sort* s);

    _Z3_ast* Z3_mk_forall_const(
        _Z3_context* c,
        unsigned weight,
        unsigned num_bound,
        _Z3_app* const bound[],
        unsigned num_patterns,
        _Z3_pattern* const patterns[],
        _Z3_ast* body
    );
    _Z3_sort* Z3_get_array_sort_range(_Z3_context* c, _Z3_sort* t);
    Z3_sort_kind Z3_get_sort_kind(_Z3_context* c, _Z3_sort* t);
    _Z3_ast* Z3_mk_set_difference(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_ast* Z3_mk_set_subset(_Z3_context* c, _Z3_ast* arg1, _Z3_ast* arg2);
    _Z3_ast* Z3_mk_set_complement(_Z3_context* c, _Z3_ast* arg);
    _Z3_ast* Z3_mk_set_intersect(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_set_union(_Z3_context* c, unsigned num_args, _Z3_ast* const args[]);
    _Z3_ast* Z3_mk_set_member(_Z3_context* c, _Z3_ast* elem, _Z3_ast* set);
    _Z3_ast* Z3_mk_set_add(_Z3_context* c, _Z3_ast* set, _Z3_ast* elem);
    _Z3_ast* Z3_mk_const_array(_Z3_context* c, _Z3_sort* domain, _Z3_ast* v);
    _Z3_ast* Z3_mk_store(_Z3_context* c, _Z3_ast* a, _Z3_ast* i, _Z3_ast* v);
    _Z3_ast* Z3_mk_select(_Z3_context* c, _Z3_ast* a, _Z3_ast* i);
    _Z3_ast* Z3_mk_zero_ext(_Z3_context* c, unsigned i, _Z3_ast* t1);
    _Z3_ast* Z3_mk_extract(_Z3_context* c, unsigned high, unsigned low, _Z3_ast* t1);
    _Z3_ast* Z3_mk_sign_ext(_Z3_context* c, unsigned i, _Z3_ast* t1);
    _Z3_ast* Z3_mk_bvmul_no_underflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsdiv_no_overflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsub_no_overflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsub_no_underflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2, bool is_signed);
    _Z3_ast* Z3_mk_bvadd_no_underflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvmul_no_overflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2, bool is_signed);
    _Z3_ast* Z3_mk_bvadd_no_overflow(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2, bool is_signed);
    _Z3_ast* Z3_mk_bvneg_no_overflow(_Z3_context* c, _Z3_ast* t1);

    _Z3_ast* Z3_mk_concat(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_ext_rotate_left(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_ext_rotate_right(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvashr(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvlshr(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvshl(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsgt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvugt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsge(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvuge(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsle(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvule(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvslt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvult(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsmod(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsrem(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvurem(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsdiv(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvudiv(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvmul(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvsub(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvadd(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvxnor(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvnor(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvnand(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvxor(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvor(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bvand(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_bv2int(_Z3_context* c, _Z3_ast* t1, bool is_signed);
    _Z3_ast* Z3_mk_real2int(_Z3_context* c, _Z3_ast* t1);

    _Z3_ast* Z3_mk_bvredor(_Z3_context* c, _Z3_ast* t1);
    _Z3_ast* Z3_mk_bvredand(_Z3_context* c, _Z3_ast* t1);
    _Z3_ast* Z3_mk_bvneg(_Z3_context* c, _Z3_ast* t1);
    _Z3_ast* Z3_mk_bvnot(_Z3_context* c, _Z3_ast* t1);
    _Z3_ast* Z3_mk_int2bv(_Z3_context* c, unsigned n, _Z3_ast* t1);
    unsigned Z3_get_bv_sort_size(_Z3_context* c, _Z3_sort* t);

    bool Z3_get_numeral_int64(_Z3_context* c, _Z3_ast* v, int64_t* i);

    bool Z3_get_numeral_uint64(_Z3_context* c, _Z3_ast* v, uint64_t* u);
    _Z3_ast* Z3_mk_string(_Z3_context* c, const char* s);
    char* Z3_get_string(_Z3_context* c, _Z3_ast* s);
    char* Z3_func_decl_to_string(_Z3_context* c, _Z3_func_decl* d);
    char* Z3_func_decl_to_ast(_Z3_context* c, _Z3_func_decl* f);

    _Z3_ast* Z3_mk_seq_suffix(_Z3_context* c, _Z3_ast* suffix, _Z3_ast* s);
    _Z3_ast* Z3_mk_seq_prefix(_Z3_context* c, _Z3_ast* suffix, _Z3_ast* s);
    _Z3_ast* Z3_mk_seq_contains(_Z3_context* c, _Z3_ast* container, _Z3_ast* containee);
    _Z3_ast* Z3_mk_seq_concat(_Z3_context* c, unsigned n, _Z3_ast* const args[]);


    _Z3_tactic* Z3_mk_tactic(_Z3_context* c, const char* name);
    void Z3_tactic_dec_ref(_Z3_context* c, _Z3_tactic* g);
    void Z3_tactic_inc_ref(_Z3_context* c, _Z3_tactic* g);
    const char* Z3_tactic_get_help(_Z3_context* c, _Z3_tactic* t);
    _Z3_apply_result* Z3_tactic_apply_ex(_Z3_context* c, _Z3_tactic* t, _Z3_goal* g, _Z3_params* p);


    _Z3_func_decl* Z3_get_app_decl(_Z3_context* c, _Z3_app* a);

    _Z3_ast* Z3_mk_fpa_numeral_float(_Z3_context* c, float v, _Z3_sort* ty);
    _Z3_ast* Z3_mk_fpa_numeral_double(_Z3_context* c, double v, _Z3_sort* ty);
    _Z3_ast* Z3_mk_fpa_div(_Z3_context* c, _Z3_ast* rm, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_mul(_Z3_context* c, _Z3_ast* rm, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_sub(_Z3_context* c, _Z3_ast* rm, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_add(_Z3_context* c, _Z3_ast* rm, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_gt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_lt(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    _Z3_ast* Z3_mk_fpa_neg(_Z3_context* c, _Z3_ast* t);
    _Z3_ast* Z3_mk_fpa_abs(_Z3_context* c, _Z3_ast* t);
    _Z3_ast* Z3_mk_fpa_round_toward_positive(_Z3_context* c);
    _Z3_ast* Z3_mk_fpa_round_toward_negative(_Z3_context* c);
    _Z3_ast* Z3_mk_fpa_round_toward_zero(_Z3_context* c);
}
