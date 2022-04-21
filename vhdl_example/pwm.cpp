#include "Vpwm_top.h"
#include "verilated.h"
#include "verilated_fst_c.h"

int main(int argc, char** argv, char** env) {
  vluint64_t main_time = 0;
  Verilated::commandArgs(argc, argv);
  Vpwm_top *top = new Vpwm_top;
  VerilatedFstC* tfp = new VerilatedFstC;
  Verilated::traceEverOn(true);
  top->trace(tfp, 99);  // Trace 99 levels of hierarchy
  tfp->open("obj_dir/pwm.fst");
  top->clk = 0;
  top->duty = 0;
  for(long cycles = 0; cycles < 10000000; cycles++) {
    top->clk = 0;
    if (cycles % 65536 == 0)
        top->duty += 10;
    top->eval();
    main_time += 5;
    tfp->dump(main_time);

    top->clk = 1;
    top->eval();
    main_time += 5;
    tfp->dump(main_time);
    if (Verilated::gotFinish())
        break;
  }
  delete top;
  exit(0);
}
