module fifo_top ;
  bit clk ;

  initial begin
    clk = 0 ;
    forever begin
      #1 clk = ~clk ;
    end
  end

  fifo_if fif (clk) ;
  fifo DUT (fif);
  fifo_tb TEST (fif);
  fifo_monitor MON (fif);
  
endmodule