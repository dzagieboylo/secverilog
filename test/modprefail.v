`include "internal2.vh"


module modprefail(
	     input  {L} clk,
	     input  {H} high_in,
	     output {L} sink_l
	     );   

   internal int1
     (
      .d_in (high_in), //this should fail due to precond that L(d_in) <= L
      .d_out (sink_l)
      );

   
endmodule
