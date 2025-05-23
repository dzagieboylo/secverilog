`include "internal.vh"

module inferfail(
	     input {L} clk,
	     input cond,
	     input {L} low_in,
	     input {H} high_in,
	     output {L} sink
	     );   

   reg	store_implicit; //should infer seq type

   always@(posedge clk) begin
      if (cond) begin
	 store_implicit <= high_in;  //error here if {L} inferred for store_implicit
      end else begin
	 store_implicit <= low_in;
      end
   end

   assign sink = store_implicit; //error here if {H} inferred for store_implicit
   
endmodule
