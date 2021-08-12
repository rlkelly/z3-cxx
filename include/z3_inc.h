#pragma once

#include <cinttypes>

extern "C" {
    typedef enum
    {
        Z3_GOAL_PRECISE,
        Z3_GOAL_UNDER,
        Z3_GOAL_OVER,
        Z3_GOAL_UNDER_OVER
    } Z3_goal_prec;
    typedef enum {
        // Basic
        Z3_OP_TRUE = 0x100,
        Z3_OP_FALSE,
        Z3_OP_EQ,
        Z3_OP_DISTINCT,
        Z3_OP_ITE,
        Z3_OP_AND,
        Z3_OP_OR,
        Z3_OP_IFF,
        Z3_OP_XOR,
        Z3_OP_NOT,
        Z3_OP_IMPLIES,
        Z3_OP_OEQ,

        // Arithmetic
        Z3_OP_ANUM = 0x200,
        Z3_OP_AGNUM,
        Z3_OP_LE,
        Z3_OP_GE,
        Z3_OP_LT,
        Z3_OP_GT,
        Z3_OP_ADD,
        Z3_OP_SUB,
        Z3_OP_UMINUS,
        Z3_OP_MUL,
        Z3_OP_DIV,
        Z3_OP_IDIV,
        Z3_OP_REM,
        Z3_OP_MOD,
        Z3_OP_TO_REAL,
        Z3_OP_TO_INT,
        Z3_OP_IS_INT,
        Z3_OP_POWER,

        // Arrays & Sets
        Z3_OP_STORE = 0x300,
        Z3_OP_SELECT,
        Z3_OP_CONST_ARRAY,
        Z3_OP_ARRAY_MAP,
        Z3_OP_ARRAY_DEFAULT,
        Z3_OP_SET_UNION,
        Z3_OP_SET_INTERSECT,
        Z3_OP_SET_DIFFERENCE,
        Z3_OP_SET_COMPLEMENT,
        Z3_OP_SET_SUBSET,
        Z3_OP_AS_ARRAY,
        Z3_OP_ARRAY_EXT,
        Z3_OP_SET_HAS_SIZE,
        Z3_OP_SET_CARD,

        // Bit-vectors
        Z3_OP_BNUM = 0x400,
        Z3_OP_BIT1,
        Z3_OP_BIT0,
        Z3_OP_BNEG,
        Z3_OP_BADD,
        Z3_OP_BSUB,
        Z3_OP_BMUL,

        Z3_OP_BSDIV,
        Z3_OP_BUDIV,
        Z3_OP_BSREM,
        Z3_OP_BUREM,
        Z3_OP_BSMOD,

        // special functions to record the division by 0 cases
        // these are internal functions
        Z3_OP_BSDIV0,
        Z3_OP_BUDIV0,
        Z3_OP_BSREM0,
        Z3_OP_BUREM0,
        Z3_OP_BSMOD0,

        Z3_OP_ULEQ,
        Z3_OP_SLEQ,
        Z3_OP_UGEQ,
        Z3_OP_SGEQ,
        Z3_OP_ULT,
        Z3_OP_SLT,
        Z3_OP_UGT,
        Z3_OP_SGT,

        Z3_OP_BAND,
        Z3_OP_BOR,
        Z3_OP_BNOT,
        Z3_OP_BXOR,
        Z3_OP_BNAND,
        Z3_OP_BNOR,
        Z3_OP_BXNOR,

        Z3_OP_CONCAT,
        Z3_OP_SIGN_EXT,
        Z3_OP_ZERO_EXT,
        Z3_OP_EXTRACT,
        Z3_OP_REPEAT,

        Z3_OP_BREDOR,
        Z3_OP_BREDAND,
        Z3_OP_BCOMP,

        Z3_OP_BSHL,
        Z3_OP_BLSHR,
        Z3_OP_BASHR,
        Z3_OP_ROTATE_LEFT,
        Z3_OP_ROTATE_RIGHT,
        Z3_OP_EXT_ROTATE_LEFT,
        Z3_OP_EXT_ROTATE_RIGHT,

        Z3_OP_BIT2BOOL,
        Z3_OP_INT2BV,
        Z3_OP_BV2INT,
        Z3_OP_CARRY,
        Z3_OP_XOR3,

        Z3_OP_BSMUL_NO_OVFL,
        Z3_OP_BUMUL_NO_OVFL,
        Z3_OP_BSMUL_NO_UDFL,
        Z3_OP_BSDIV_I,
        Z3_OP_BUDIV_I,
        Z3_OP_BSREM_I,
        Z3_OP_BUREM_I,
        Z3_OP_BSMOD_I,

        // Proofs
        Z3_OP_PR_UNDEF = 0x500,
        Z3_OP_PR_TRUE,
        Z3_OP_PR_ASSERTED,
        Z3_OP_PR_GOAL,
        Z3_OP_PR_MODUS_PONENS,
        Z3_OP_PR_REFLEXIVITY,
        Z3_OP_PR_SYMMETRY,
        Z3_OP_PR_TRANSITIVITY,
        Z3_OP_PR_TRANSITIVITY_STAR,
        Z3_OP_PR_MONOTONICITY,
        Z3_OP_PR_QUANT_INTRO,
        Z3_OP_PR_BIND,
        Z3_OP_PR_DISTRIBUTIVITY,
        Z3_OP_PR_AND_ELIM,
        Z3_OP_PR_NOT_OR_ELIM,
        Z3_OP_PR_REWRITE,
        Z3_OP_PR_REWRITE_STAR,
        Z3_OP_PR_PULL_QUANT,
        Z3_OP_PR_PUSH_QUANT,
        Z3_OP_PR_ELIM_UNUSED_VARS,
        Z3_OP_PR_DER,
        Z3_OP_PR_QUANT_INST,
        Z3_OP_PR_HYPOTHESIS,
        Z3_OP_PR_LEMMA,
        Z3_OP_PR_UNIT_RESOLUTION,
        Z3_OP_PR_IFF_TRUE,
        Z3_OP_PR_IFF_FALSE,
        Z3_OP_PR_COMMUTATIVITY,
        Z3_OP_PR_DEF_AXIOM,
        Z3_OP_PR_ASSUMPTION_ADD,
        Z3_OP_PR_LEMMA_ADD,
        Z3_OP_PR_REDUNDANT_DEL,
        Z3_OP_PR_CLAUSE_TRAIL,
        Z3_OP_PR_DEF_INTRO,
        Z3_OP_PR_APPLY_DEF,
        Z3_OP_PR_IFF_OEQ,
        Z3_OP_PR_NNF_POS,
        Z3_OP_PR_NNF_NEG,
        Z3_OP_PR_SKOLEMIZE,
        Z3_OP_PR_MODUS_PONENS_OEQ,
        Z3_OP_PR_TH_LEMMA,
        Z3_OP_PR_HYPER_RESOLVE,

        // Relational algebra
        Z3_OP_RA_STORE = 0x600,
        Z3_OP_RA_EMPTY,
        Z3_OP_RA_IS_EMPTY,
        Z3_OP_RA_JOIN,
        Z3_OP_RA_UNION,
        Z3_OP_RA_WIDEN,
        Z3_OP_RA_PROJECT,
        Z3_OP_RA_FILTER,
        Z3_OP_RA_NEGATION_FILTER,
        Z3_OP_RA_RENAME,
        Z3_OP_RA_COMPLEMENT,
        Z3_OP_RA_SELECT,
        Z3_OP_RA_CLONE,
        Z3_OP_FD_CONSTANT,
        Z3_OP_FD_LT,

        // Sequences
        Z3_OP_SEQ_UNIT,
        Z3_OP_SEQ_EMPTY,
        Z3_OP_SEQ_CONCAT,
        Z3_OP_SEQ_PREFIX,
        Z3_OP_SEQ_SUFFIX,
        Z3_OP_SEQ_CONTAINS,
        Z3_OP_SEQ_EXTRACT,
        Z3_OP_SEQ_REPLACE,
        Z3_OP_SEQ_AT,
        Z3_OP_SEQ_NTH,
        Z3_OP_SEQ_LENGTH,
        Z3_OP_SEQ_INDEX,
        Z3_OP_SEQ_LAST_INDEX,
        Z3_OP_SEQ_TO_RE,
        Z3_OP_SEQ_IN_RE,

        // strings
        Z3_OP_STR_TO_INT,
        Z3_OP_INT_TO_STR,
        Z3_OP_UBV_TO_STR,
        Z3_OP_SBV_TO_STR,
        Z3_OP_STRING_LT,
        Z3_OP_STRING_LE,

        // regular expressions
        Z3_OP_RE_PLUS,
        Z3_OP_RE_STAR,
        Z3_OP_RE_OPTION,
        Z3_OP_RE_CONCAT,
        Z3_OP_RE_UNION,
        Z3_OP_RE_RANGE,
        Z3_OP_RE_LOOP,
        Z3_OP_RE_INTERSECT,
        Z3_OP_RE_EMPTY_SET,
        Z3_OP_RE_FULL_SET,
        Z3_OP_RE_COMPLEMENT,

        // Auxiliary
        Z3_OP_LABEL = 0x700,
        Z3_OP_LABEL_LIT,

        // Datatypes
        Z3_OP_DT_CONSTRUCTOR=0x800,
        Z3_OP_DT_RECOGNISER,
        Z3_OP_DT_IS,
        Z3_OP_DT_ACCESSOR,
        Z3_OP_DT_UPDATE_FIELD,

        // Pseudo Booleans
        Z3_OP_PB_AT_MOST=0x900,
        Z3_OP_PB_AT_LEAST,
        Z3_OP_PB_LE,
        Z3_OP_PB_GE,
        Z3_OP_PB_EQ,

        // Special relations
        Z3_OP_SPECIAL_RELATION_LO = 0xa000,
        Z3_OP_SPECIAL_RELATION_PO,
        Z3_OP_SPECIAL_RELATION_PLO,
        Z3_OP_SPECIAL_RELATION_TO,
        Z3_OP_SPECIAL_RELATION_TC,
        Z3_OP_SPECIAL_RELATION_TRC,


        // Floating-Point Arithmetic
        Z3_OP_FPA_RM_NEAREST_TIES_TO_EVEN = 0xb000,
        Z3_OP_FPA_RM_NEAREST_TIES_TO_AWAY,
        Z3_OP_FPA_RM_TOWARD_POSITIVE,
        Z3_OP_FPA_RM_TOWARD_NEGATIVE,
        Z3_OP_FPA_RM_TOWARD_ZERO,

        Z3_OP_FPA_NUM,
        Z3_OP_FPA_PLUS_INF,
        Z3_OP_FPA_MINUS_INF,
        Z3_OP_FPA_NAN,
        Z3_OP_FPA_PLUS_ZERO,
        Z3_OP_FPA_MINUS_ZERO,

        Z3_OP_FPA_ADD,
        Z3_OP_FPA_SUB,
        Z3_OP_FPA_NEG,
        Z3_OP_FPA_MUL,
        Z3_OP_FPA_DIV,
        Z3_OP_FPA_REM,
        Z3_OP_FPA_ABS,
        Z3_OP_FPA_MIN,
        Z3_OP_FPA_MAX,
        Z3_OP_FPA_FMA,
        Z3_OP_FPA_SQRT,
        Z3_OP_FPA_ROUND_TO_INTEGRAL,

        Z3_OP_FPA_EQ,
        Z3_OP_FPA_LT,
        Z3_OP_FPA_GT,
        Z3_OP_FPA_LE,
        Z3_OP_FPA_GE,
        Z3_OP_FPA_IS_NAN,
        Z3_OP_FPA_IS_INF,
        Z3_OP_FPA_IS_ZERO,
        Z3_OP_FPA_IS_NORMAL,
        Z3_OP_FPA_IS_SUBNORMAL,
        Z3_OP_FPA_IS_NEGATIVE,
        Z3_OP_FPA_IS_POSITIVE,

        Z3_OP_FPA_FP,
        Z3_OP_FPA_TO_FP,
        Z3_OP_FPA_TO_FP_UNSIGNED,
        Z3_OP_FPA_TO_UBV,
        Z3_OP_FPA_TO_SBV,
        Z3_OP_FPA_TO_REAL,

        Z3_OP_FPA_TO_IEEE_BV,

        Z3_OP_FPA_BVWRAP,
        Z3_OP_FPA_BV2RM,

        Z3_OP_INTERNAL,

        Z3_OP_UNINTERPRETED
    } Z3_decl_kind;

    typedef enum
    {
        Z3_INT_SYMBOL,
        Z3_STRING_SYMBOL
    } Z3_symbol_kind;

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
    _Z3_ast* Z3_sort_to_ast(_Z3_context* c, _Z3_sort* s);
    bool Z3_is_eq_sort(_Z3_context* c, _Z3_sort* s1, _Z3_sort* s2);
    const char* Z3_sort_to_string(_Z3_context* c, _Z3_sort* s);
    _Z3_sort* Z3_get_array_sort_range(_Z3_context* c, _Z3_sort* t);
    _Z3_sort* Z3_get_array_sort_domain(_Z3_context* c, _Z3_sort* t);

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
    void Z3_solver_dec_ref(_Z3_context* c, _Z3_solver* s);
    void Z3_solver_inc_ref(_Z3_context* c, _Z3_solver* s);
    const char* Z3_solver_to_string(_Z3_context* c, _Z3_solver* s);
    void Z3_solver_set_params(_Z3_context* c, _Z3_solver* s, _Z3_params* p);
    const char* Z3_solver_get_reason_unknown(_Z3_context* c, _Z3_solver* s);
    _Z3_ast* Z3_solver_get_proof(_Z3_context* c, _Z3_solver* s);
    void Z3_solver_pop(_Z3_context* c, _Z3_solver* s, unsigned n);
    void Z3_solver_push(_Z3_context* c, _Z3_solver* s);
    _Z3_ast_vector* Z3_solver_get_unsat_core(_Z3_context* c, _Z3_solver* s);
    Z3_lbool Z3_solver_check_assumptions(_Z3_context* c, _Z3_solver* s,
                                                unsigned num_assumptions, _Z3_ast* const assumptions[]);
    void Z3_solver_reset(_Z3_context* c, _Z3_solver* s);
    void Z3_solver_assert_and_track(_Z3_context* c, _Z3_solver* s, _Z3_ast* a, _Z3_ast* p);
    _Z3_solver* Z3_solver_translate(_Z3_context* source, _Z3_solver* s, _Z3_context* target);
    _Z3_solver* Z3_mk_solver(_Z3_context* c);

    _Z3_model* Z3_solver_get_model(_Z3_context* c, _Z3_solver* s);
    char* Z3_model_to_string(_Z3_context* c, _Z3_model* m);
    char* Z3_ast_to_string(_Z3_context* c, _Z3_ast* a);
    bool Z3_is_eq_ast(_Z3_context* c, _Z3_ast* t1, _Z3_ast* t2);
    unsigned Z3_get_ast_hash(_Z3_context* c, _Z3_ast* a);
    unsigned Z3_get_ast_id(_Z3_context* c, _Z3_ast* t);

    const char* Z3_pattern_to_string(_Z3_context* c, _Z3_pattern* p);
    _Z3_pattern* Z3_mk_pattern(_Z3_context* c, unsigned num_patterns, _Z3_ast* const terms[]);

    bool Z3_model_eval(_Z3_context* c, _Z3_model* m, _Z3_ast* t, bool model_completion, _Z3_ast ** v);

    bool Z3_get_numeral_int(_Z3_context* c, _Z3_ast* v, int* i);
    int Z3_get_symbol_int(_Z3_context* c, _Z3_symbol* s);
    const char* Z3_get_symbol_string(_Z3_context* c, _Z3_symbol* s);
    Z3_symbol_kind Z3_get_symbol_kind(_Z3_context* c, _Z3_symbol* s);
    _Z3_symbol* Z3_get_decl_name(_Z3_context* c, _Z3_func_decl* d);
    Z3_decl_kind Z3_get_decl_kind(_Z3_context* c, _Z3_func_decl* d);
    _Z3_ast* Z3_mk_app(
        _Z3_context* c,
        _Z3_func_decl* d,
        unsigned num_args,
        _Z3_ast* const args[]);
    unsigned Z3_get_arity(_Z3_context* c, _Z3_func_decl* d);

    Z3_ast_kind Z3_get_ast_kind(_Z3_context* c, _Z3_ast* a);

    void Z3_global_param_reset_all(void);

    _Z3_func_decl* Z3_mk_func_decl(_Z3_context* c, _Z3_symbol* s,
                                    unsigned domain_size, _Z3_sort* const domain[],
                                    _Z3_sort* range);


    _Z3_sort* Z3_get_sort(_Z3_context* c, _Z3_ast* a);
    bool Z3_is_string_sort(_Z3_context* c, _Z3_sort* s);

    _Z3_sort* Z3_mk_bool_sort(_Z3_context* c);
    _Z3_sort* Z3_mk_int_sort(_Z3_context* c);
    _Z3_sort* Z3_mk_real_sort(_Z3_context* c);
    _Z3_sort* Z3_mk_string_sort(_Z3_context* c);

    _Z3_sort* Z3_mk_set_sort(_Z3_context* c, _Z3_sort* ty);
    _Z3_sort* Z3_mk_array_sort(_Z3_context* c, _Z3_sort* domain, _Z3_sort* range);
    _Z3_sort* Z3_mk_bv_sort(_Z3_context* c, unsigned sz);
    _Z3_sort* Z3_mk_uninterpreted_sort(_Z3_context* c, _Z3_symbol* s);

    void Z3_apply_result_dec_ref(_Z3_context* c, _Z3_apply_result* r);
    void Z3_apply_result_inc_ref(_Z3_context* c, _Z3_apply_result* r);


    _Z3_ast* Z3_mk_forall_const(
        _Z3_context* c,
        unsigned weight,
        unsigned num_bound,
        _Z3_app* const bound[],
        unsigned num_patterns,
        _Z3_pattern* const patterns[],
        _Z3_ast* body
    );
    Z3_sort_kind Z3_get_sort_kind(_Z3_context* c, _Z3_sort* t);
    _Z3_sort* Z3_mk_enumeration_sort(_Z3_context* c,
                                          _Z3_symbol* name,
                                          unsigned n,
                                          _Z3_symbol*  const enum_names[],
                                          _Z3_func_decl* enum_consts[],
                                          _Z3_func_decl* enum_testers[]);
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

    _Z3_ast* Z3_mk_seq_suffix(_Z3_context* c, _Z3_ast* suffix, _Z3_ast* s);
    _Z3_ast* Z3_mk_seq_prefix(_Z3_context* c, _Z3_ast* suffix, _Z3_ast* s);
    _Z3_ast* Z3_mk_seq_contains(_Z3_context* c, _Z3_ast* container, _Z3_ast* containee);
    _Z3_ast* Z3_mk_seq_concat(_Z3_context* c, unsigned n, _Z3_ast* const args[]);


    _Z3_tactic* Z3_mk_tactic(_Z3_context* c, const char* name);
    void Z3_tactic_dec_ref(_Z3_context* c, _Z3_tactic* g);
    void Z3_tactic_inc_ref(_Z3_context* c, _Z3_tactic* g);
    const char* Z3_tactic_get_help(_Z3_context* c, _Z3_tactic* t);
    _Z3_apply_result* Z3_tactic_apply_ex(_Z3_context* c, _Z3_tactic* t, _Z3_goal* g, _Z3_params* p);
    _Z3_apply_result* Z3_tactic_apply(_Z3_context* c, _Z3_tactic* t, _Z3_goal* g);
    _Z3_tactic* Z3_tactic_fail_if(_Z3_context* c, _Z3_probe* p);
    _Z3_tactic* Z3_tactic_cond(_Z3_context* c, _Z3_probe* p, _Z3_tactic* t1, _Z3_tactic* t2);
    _Z3_tactic* Z3_tactic_when(_Z3_context* c, _Z3_probe* p, _Z3_tactic* t);
    _Z3_tactic* Z3_tactic_or_else(_Z3_context* c, _Z3_tactic* t1, _Z3_tactic* t2);
    _Z3_tactic* Z3_tactic_and_then(_Z3_context* c, _Z3_tactic* t1, _Z3_tactic* t2);
    _Z3_tactic* Z3_tactic_repeat(_Z3_context* c, _Z3_tactic* t, unsigned max);
    _Z3_tactic* Z3_tactic_fail(_Z3_context* c);
    _Z3_tactic* Z3_tactic_skip(_Z3_context* c);
    const char* Z3_get_tactic_name(_Z3_context* c, unsigned i);

    const char* Z3_get_probe_name(_Z3_context* c, unsigned i);
    void Z3_probe_dec_ref(_Z3_context* c, _Z3_probe* p);
    void Z3_probe_inc_ref(_Z3_context* c, _Z3_probe* p);
    _Z3_probe* Z3_probe_not(_Z3_context* x, _Z3_probe* p);
    _Z3_probe* Z3_probe_eq(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_or(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_and(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_ge(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_le(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_gt(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_lt(_Z3_context* x, _Z3_probe* p1, _Z3_probe* p2);
    _Z3_probe* Z3_probe_const(_Z3_context* x, double val);
    double Z3_probe_apply(_Z3_context* c, _Z3_probe* p, _Z3_goal* g);
    _Z3_probe* Z3_mk_probe(_Z3_context* c, const char* name);
    const char* Z3_probe_get_descr(_Z3_context* c, const char* name);
    unsigned Z3_get_num_probes(_Z3_context* c);

    _Z3_constructor_list* Z3_mk_constructor_list(_Z3_context* c,
                                                      unsigned num_constructors,
                                                      _Z3_constructor* const constructors[]);

    void Z3_del_constructor_list(_Z3_context* c, _Z3_constructor_list* clist);
    void Z3_del_constructor(_Z3_context* c, _Z3_constructor* constr);
    _Z3_func_decl* Z3_get_datatype_sort_constructor_accessor(_Z3_context* c,
                                                                  _Z3_sort* t,
                                                                  unsigned idx_c,
                                                                  unsigned idx_a);
    _Z3_func_decl* Z3_get_datatype_sort_recognizer(
        _Z3_context* c, _Z3_sort* t, unsigned idx);
    _Z3_func_decl* Z3_get_datatype_sort_constructor(
        _Z3_context* c, _Z3_sort* t, unsigned idx);
    _Z3_constructor* Z3_mk_constructor(_Z3_context* c,
                                            _Z3_symbol* name,
                                            _Z3_symbol* recognizer,
                                            unsigned num_fields,
                                            _Z3_symbol* const field_names[],
                                            _Z3_sort* const sorts[],
                                            unsigned sort_refs[]
                                            );
    void Z3_mk_datatypes(_Z3_context* c,
                                unsigned num_sorts,
                                _Z3_symbol* const sort_names[],
                                _Z3_sort* sorts[],
                                _Z3_constructor_list* constructor_lists[]);


    unsigned Z3_get_num_tactics(_Z3_context* c);
    void Z3_goal_inc_ref(_Z3_context* c, _Z3_goal* g);
    void Z3_goal_dec_ref(_Z3_context* c, _Z3_goal* g);
    _Z3_goal* Z3_apply_result_get_subgoal(_Z3_context* c, _Z3_apply_result* r, unsigned i);
    unsigned Z3_apply_result_get_num_subgoals(_Z3_context* c, _Z3_apply_result* r);
    const char* Z3_goal_to_string(_Z3_context* c, _Z3_goal* g);
    _Z3_ast* Z3_goal_formula(_Z3_context* c, _Z3_goal* g, unsigned idx);
    Z3_goal_prec Z3_goal_precision(_Z3_context* c, _Z3_goal* g);
    _Z3_goal* Z3_goal_translate(_Z3_context* source, _Z3_goal* g, _Z3_context* target);
    void Z3_goal_reset(_Z3_context* c, _Z3_goal* g);

    _Z3_goal* Z3_mk_goal(_Z3_context* c, bool models, bool unsat_cores, bool proofs);
    bool Z3_goal_is_decided_sat(_Z3_context* c, _Z3_goal* g);
    bool Z3_goal_is_decided_unsat(_Z3_context* c, _Z3_goal* g);
    void Z3_goal_assert(_Z3_context* c, _Z3_goal* g, _Z3_ast* a);
    bool Z3_goal_inconsistent(_Z3_context* c, _Z3_goal* g);
    unsigned Z3_goal_depth(_Z3_context* c, _Z3_goal* g);
    unsigned Z3_goal_size(_Z3_context* c, _Z3_goal* g);
    unsigned Z3_goal_num_exprs(_Z3_context* c, _Z3_goal* g);
    void Z3_optimize_dec_ref(_Z3_context* c, _Z3_optimize* d);

    void Z3_model_dec_ref(_Z3_context* c, _Z3_model* m);
    void Z3_model_inc_ref(_Z3_context* c, _Z3_model* m);
    _Z3_model* Z3_model_translate(_Z3_context* c, _Z3_model* m, _Z3_context* dst);


    // z3_optimization.h
    _Z3_optimize* Z3_mk_optimize(_Z3_context* c);
    const char* Z3_optimize_get_reason_unknown(_Z3_context* c, _Z3_optimize* d);
    const char* Z3_optimize_to_string(_Z3_context* c, _Z3_optimize* o);
    void Z3_optimize_dec_ref(_Z3_context* c, _Z3_optimize* d);
    void Z3_optimize_inc_ref(_Z3_context* c, _Z3_optimize* d);
    _Z3_ast_vector* Z3_optimize_get_objectives(_Z3_context* c, _Z3_optimize* o);
    Z3_lbool Z3_optimize_check(_Z3_context* c, _Z3_optimize* o, unsigned num_assumptions, _Z3_ast* const assumptions[]);
    void Z3_optimize_pop(_Z3_context* c, _Z3_optimize* d);
    void Z3_optimize_push(_Z3_context* c, _Z3_optimize* d);
    unsigned Z3_optimize_minimize(_Z3_context* c, _Z3_optimize* o, _Z3_ast* t);
    unsigned Z3_optimize_maximize(_Z3_context* c, _Z3_optimize* o, _Z3_ast* t);
    unsigned Z3_optimize_assert_soft(_Z3_context* c, _Z3_optimize* o, _Z3_ast* a, const char* weight, _Z3_symbol* id);
    void Z3_optimize_assert(_Z3_context* c, _Z3_optimize* o, _Z3_ast* a);
    _Z3_model* Z3_optimize_get_model(_Z3_context* c, _Z3_optimize* o);


    // z3_ast_containers.h
    _Z3_ast* Z3_ast_vector_get(_Z3_context* c, _Z3_ast_vector* v, unsigned i);
    unsigned Z3_ast_vector_size(_Z3_context* c, _Z3_ast_vector* v);


    _Z3_func_decl* Z3_get_app_decl(_Z3_context* c, _Z3_app* a);
    _Z3_ast* Z3_func_decl_to_ast(_Z3_context* c, _Z3_func_decl* f);

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
    unsigned Z3_fpa_get_sbits(_Z3_context* c, _Z3_sort* s);
    unsigned Z3_fpa_get_ebits(_Z3_context* c, _Z3_sort* s);
    _Z3_sort* Z3_mk_fpa_sort(_Z3_context* c, unsigned ebits, unsigned sbits);
}
