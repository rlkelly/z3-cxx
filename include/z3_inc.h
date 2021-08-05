#pragma once

extern "C" {
    struct _Z3_config;
    _Z3_config* Z3_mk_config(void);
    void Z3_global_param_reset_all(void);
}
