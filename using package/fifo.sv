////////////////////////////////////////////////////////////////////////////////
// Author: Kareem Waseem
// Course: Digital Verification using SV & UVM
//
// Description: FIFO Design 
// 
////////////////////////////////////////////////////////////////////////////////
module fifo(fifo_if.DUT fif);
 
localparam max_fifo_addr = $clog2(fif.FIFO_DEPTH);

reg [fif.FIFO_WIDTH-1:0] mem [fif.FIFO_DEPTH-1:0];

reg [max_fifo_addr-1:0] wr_ptr, rd_ptr;
reg [max_fifo_addr:0] count;

always @(posedge fif.clk or negedge fif.rst_n) begin
	if (!fif.rst_n) begin
		wr_ptr <= 0;
		// BUG DETECTED : wr_ack should be Low when reset is asserted .
		fif.wr_ack <= 0 ;
		// BUG DETECTED : overflow should be Low when reset is asserted .
		fif.overflow <= 0 ;

	end
	// Writing Block 
	else if (fif.wr_en && count < fif.FIFO_DEPTH ) begin
		mem[wr_ptr] <= fif.data_in;
		fif.wr_ack <= 1;
		wr_ptr <= wr_ptr + 1;
	end
	else begin 
		fif.wr_ack <= 0; 
		if (fif.full & fif.wr_en)
			fif.overflow <= 1;
		else
			fif.overflow <= 0;
	end
end


// Reading Block 
always @(posedge fif.clk or negedge fif.rst_n) begin
	if (!fif.rst_n) begin
		rd_ptr <= 0;
		// BUG DETECTED : Underflow should be Low when reset is asserted .
		fif.underflow <= 0 ;
	end
	else if (fif.rd_en && count != 0 ) begin
		fif.data_out <= mem[rd_ptr];
		rd_ptr <= rd_ptr + 1;
	end
	// BUG DETECTED : Underflow output should be Sequential .
	else begin 
		if (fif.empty & fif.rd_en)
			fif.underflow <= 1;
		else
			fif.underflow <= 0;
end
end

always @(posedge fif.clk or negedge fif.rst_n) begin
	if (!fif.rst_n) begin
		count <= 0;
	end
	else begin
		if	( ({fif.wr_en, fif.rd_en} == 2'b10) && !fif.full) 
			count <= count + 1;
		else if ( ({fif.wr_en, fif.rd_en} == 2'b01) && !fif.empty)
			count <= count - 1;
			// BUG DETECTED : Uncovered case when both wr_en and rd_en are high and FIFO if full , Reading process happens .
			else if ( ({fif.wr_en, fif.rd_en} == 2'b11) && fif.full)
			count <= count - 1;
			//BUG DETECTED : Uncovered case when both wr_en and rd_en are high and FIFO if empty , Writing process happens .
			else if ( ({fif.wr_en, fif.rd_en} == 2'b11) && fif.empty)
			count <= count + 1;

	end
end

assign fif.full = (count == fif.FIFO_DEPTH)? 1 : 0;
assign fif.empty = (count == 0)? 1 : 0;
//BUG DETECTED : almostfull is high when there is two spots empty , while it should be only one .
assign fif.almostfull = (count == fif.FIFO_DEPTH-1)? 1 : 0; 
assign fif.almostempty = (count == 1)? 1 : 0;

//Assertions 

    property reset_check;
        @(posedge fif.clk) (!fif.rst_n) |=> (wr_ptr == 0 && rd_ptr == 0 && count == 0);
    endproperty
    assert property (reset_check) else $error(" error in rst ");
    cover property (reset_check);

    property check1;
       @(posedge fif.clk) disable iff (!fif.rst_n)
           ( fif.wr_en && count < fif.FIFO_DEPTH ) |=> 
              (fif.wr_ack == 1);
    endproperty
    assert property (check1) else $error("error in check1");
    cover property (check1);	

    property check2;
       @(posedge fif.clk) disable iff (!fif.rst_n)
           ( fif.wr_en && fif.full ) |=> 
              (fif.overflow == 1);
    endproperty
    assert property (check2) else $error("error in check2");
    cover property (check2);

    property check3;
        @(posedge fif.clk) disable iff (!fif.rst_n)
            ( fif.rd_en && fif.empty ) |=> 
               (fif.underflow == 1);
    endproperty
    assert property (check3) else $error("error in check3");
    cover property (check3);

    property check4;
        @(posedge fif.clk) disable iff (!fif.rst_n)
            ( count == 0 ) |-> 
               (fif.empty);
     endproperty
     assert property (check4) else $error("error in check4");
     cover property (check4);

     property check5;
        @(posedge fif.clk) disable iff (!fif.rst_n)
           ( count == fif.FIFO_DEPTH ) |-> 
              (fif.full);
      endproperty
      assert property (check5) else $error("error in check5");
      cover property (check5);

     property check6;
        @(posedge fif.clk) disable iff (!fif.rst_n)
           ( count == fif.FIFO_DEPTH - 1) |-> 
                (fif.almostfull);
     endproperty
     assert property (check6) else $error("error in check6");
     cover property (check6);

     property check7;
        @(posedge fif.clk) disable iff (!fif.rst_n)
            ( count == 1 ) |-> 
               (fif.almostempty);
     endproperty
     assert property (check7) else $error("error in check7");
     cover property (check7);

    property check8;
        @(posedge fif.clk) disable iff (!fif.rst_n)
            ( wr_ptr == 7 ) |-> (wr_ptr == 0) [=1];
     endproperty
     assert property (check8) else $error("error in check8");
     cover property (check8);

     property check9;
        @(posedge fif.clk) disable iff (!fif.rst_n)
           ( rd_ptr == 7 ) |-> (rd_ptr == 0) [=1];
     endproperty
     assert property (check9) else $error("error in check9");
     cover property (check9);

     property check10;
        @(posedge fif.clk) disable iff (!fif.rst_n)
            ( count == 8 ) |-> (count == 0 || count == 7) [=1] ;
     endproperty
     assert property (check10) else $error("error in check10");
     cover property (check10);

     property check11;
         @(posedge fif.clk) disable iff (!fif.rst_n)
            ( (fif.wr_en && count < fif.FIFO_DEPTH) ) 
		       |=> ( mem[$past(wr_ptr)] <= $past(fif.data_in) );
     endproperty
     assert property (check11) else $error("error in check11");
     cover property (check11);

     property check12 ;
	    @(posedge fif.clk) disable iff (!fif.rst_n)
	         (wr_ptr < fif.FIFO_DEPTH) ;
      endproperty
     assert property (check12 ) else $error("error in check12 ");
     cover property (check12 );

      property check13 ;
	    @(posedge fif.clk) disable iff (!fif.rst_n)
	        (rd_ptr < fif.FIFO_DEPTH) ;
      endproperty
     assert property (check13) else $error("error in check13");
     cover property (check13);	  

     property check14 ;
	     @(posedge fif.clk) disable iff (!fif.rst_n)
	        (count <= fif.FIFO_DEPTH) ;
    endproperty
     assert property (check14) else $error("error in check14");
     cover property (check14);	

     property check15;
	    @(posedge fif.clk) disable iff (!fif.rst_n)
	          ( ({fif.wr_en, fif.rd_en} == 2'b10) && !fif.full) || ( ({fif.wr_en, fif.rd_en} == 2'b11) && fif.empty)
	               |=> (count == $past(count)+1);
      endproperty
     assert property (check15) else $error("error in check15");
     cover property (check15);	  

     property check16;
	     @(posedge fif.clk) disable iff (!fif.rst_n)
	         ( ({fif.wr_en, fif.rd_en} == 2'b01) && !fif.empty) || ( ({fif.wr_en, fif.rd_en} == 2'b11) && fif.full)
	              |=> (count == $past(count)-1);
       endproperty
     assert property (check16) else $error("error in check16");
     cover property (check16);

endmodule