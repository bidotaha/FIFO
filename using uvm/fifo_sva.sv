module fifo_sva ( fifo_if.DUT fifoif );
    
    property reset_check;
        @(posedge fifoif.clk) (!fifoif.rst_n) |=> (fifo.wr_ptr == 0 && fifo.rd_ptr == 0 && fifo.count == 0);
    endproperty
    assert property (reset_check) else $error(" error in rst ");
    cover property (reset_check);

    property check1;
       @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
           ( fifoif.wr_en && fifo.count < fifoif.FIFO_DEPTH ) |=> 
              (fifoif.wr_ack == 1);
    endproperty
    assert property (check1) else $error("error in check1");
    cover property (check1);	

    property check2;
       @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
           ( fifoif.wr_en && fifoif.full ) |=> 
              (fifoif.overflow == 1);
    endproperty
    assert property (check2) else $error("error in check2");
    cover property (check2);

    property check3;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( fifoif.rd_en && fifoif.empty ) |=> 
               (fifoif.underflow == 1);
    endproperty
    assert property (check3) else $error("error in check3");
    cover property (check3);

    property check4;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( fifo.count == 0 ) |-> 
               (fifoif.empty);
     endproperty
     assert property (check4) else $error("error in check4");
     cover property (check4);

     property check5;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
           ( fifo.count == fifoif.FIFO_DEPTH ) |-> 
              (fifoif.full);
      endproperty
      assert property (check5) else $error("error in check5");
      cover property (check5);

     property check6;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
           ( fifo.count == fifoif.FIFO_DEPTH - 1) |-> 
                (fifoif.almostfull);
     endproperty
     assert property (check6) else $error("error in check6");
     cover property (check6);

     property check7;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( fifo.count == 1 ) |-> 
               (fifoif.almostempty);
     endproperty
     assert property (check7) else $error("error in check7");
     cover property (check7);

    property check8;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( fifo.wr_ptr == 7 ) |-> (fifo.wr_ptr == 0) [=1];
     endproperty
     assert property (check8) else $error("error in check8");
     cover property (check8);

     property check9;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
           ( fifo.rd_ptr == 7 ) |-> (fifo.rd_ptr == 0) [=1];
     endproperty
     assert property (check9) else $error("error in check9");
     cover property (check9);

     property check10;
        @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( fifo.count == 8 ) |-> (fifo.count == 0 || fifo.count == 7) [=1] ;
     endproperty
     assert property (check10) else $error("error in check10");
     cover property (check10);

     property check11;
         @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
            ( (fifoif.wr_en && fifo.count < fifoif.FIFO_DEPTH) ) 
		       |=> ( fifo.mem[$past(fifo.wr_ptr)] <= $past(fifoif.data_in) );
     endproperty
     assert property (check11) else $error("error in check11");
     cover property (check11);

     property check12 ;
	    @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
	         (fifo.wr_ptr < fifoif.FIFO_DEPTH) ;
      endproperty
     assert property (check12 ) else $error("error in check12 ");
     cover property (check12 );

      property check13 ;
	    @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
	        (fifo.rd_ptr < fifoif.FIFO_DEPTH) ;
      endproperty
     assert property (check13) else $error("error in check13");
     cover property (check13);	  

     property check14 ;
	     @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
	        (fifo.count <= fifoif.FIFO_DEPTH) ;
    endproperty
     assert property (check14) else $error("error in check14");
     cover property (check14);	

     property check15;
	    @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
	          ( ({fifoif.wr_en, fifoif.rd_en} == 2'b10) && !fifoif.full) || ( ({fifoif.wr_en, fifoif.rd_en} == 2'b11) && fifoif.empty)
	               |=> (fifo.count == $past(fifo.count)+1);
      endproperty
     assert property (check15) else $error("error in check15");
     cover property (check15);	  

     property check16;
	     @(posedge fifoif.clk) disable iff (!fifoif.rst_n)
	         ( ({fifoif.wr_en, fifoif.rd_en} == 2'b01) && !fifoif.empty) || ( ({fifoif.wr_en, fifoif.rd_en} == 2'b11) && fifoif.full)
	              |=> (fifo.count == $past(fifo.count)-1);
       endproperty
     assert property (check16) else $error("error in check16");
     cover property (check16);

endmodule