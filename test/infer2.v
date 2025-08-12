`include "internal.vh"

module infer2(
	     input  {L} clk,
	     input  in_a,
	     input  in_b,
	     input  {H} in_high, 
	     output sink_1,
	     output sink_2,
	     output sink_3,
	     output sink_high
	     );   

   wire		    tmp1;
   wire		    tmp2;      
   assign tmp1 = in_a;
   assign tmp2 = in_b;

   reg		    r1;
   reg		    r2;   

   //TODO handle information loops r1 <= r2 <= r1...
   always@(posedge clk)
     begin
	if (r1 == 0) begin
	   r2 <= in_a | in_b;
	end else begin
	   r2 <= 0;	   
	end
     end
   always@(posedge clk)
     begin
	if (r2 == 0) begin
	   r1 <= in_a | in_b;
	end else begin
	   r1 <= 0;	   
	end
     end
   
   //Should infer: L(sink_1) = L(in_a) join L(in_b)
   //Want to make sure that L(sink_1) is not a function of L(tmp)
   assign sink_1 = tmp1 ^ tmp2;
   
   //With no refinement Should infer:
   // L(sink_2) = L(in_a) join L(in_b)
   //With refinement Should infer:
   // L(sink_2) = if (in_a) then L(in_a) join L(in_b) else L(in_a) 
   assign sink_2 = (in_a == 0) ? 0 : in_b;

   internal int1
     (
      .d_in (in_high),
      .d_out (sink_high)
      );

   //should infer L(d_out) = L(d_in)
   //then should produce constraint L(sink_high) = L(d_out)
   //which should imply L(sink_high) = H when doing z3 solving
   

   
endmodule
