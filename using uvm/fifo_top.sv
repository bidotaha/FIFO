
import uvm_pkg::*;
`include "uvm_macros.svh"
import fifo_test_pkg::*;

module fifo_top();

  bit clk;

  initial begin
    forever begin
      #1 clk = ~clk;
    end
  end
  
  fifo_if fifoif (clk);
  fifo dut (fifoif);
  bind fifo fifo_sva assertion (fifoif);

  initial begin
    uvm_config_db#(virtual fifo_if)::set(null,"uvm_test_top","fifo_IF",fifoif); 
    run_test("fifo_test");
  end

endmodule