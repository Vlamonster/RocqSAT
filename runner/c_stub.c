/* Call the C solver (c/main.c) from the runner: `rocqsat --c`. */
#include <caml/mlvalues.h>

int rocqsat_c_main(void);

value rocqsat_run_c(value unit) {
  (void) unit;
  return Val_int(rocqsat_c_main());
}
