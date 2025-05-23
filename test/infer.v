`include "internal.vh"

//Tests polymorphism of unbound labels in instantiated modules
// module internal needs to enforce in <= out but need to bind differently for each instantiation

module infer(
	     input  {L} clk,
	     input  cond,
	     input  {L} low_in,
	     input  {H} high_in,
	     output {L} sink_l,
	     output {H} sink_h
	     );   

   reg	seq {L}	   store_low;
   reg	seq {H}	   store_high;
   reg	store_implicit; //should infer seq type

   wire	tmp_h;
   wire	tmp_l;
   
   always@(posedge clk) begin
      if (cond) begin
	 store_low <= low_in;
      end else begin
	 store_low <= 0;	 
      end
   end

   always@(posedge clk) begin
      if (cond) begin
	 store_high <= low_in;
      end else begin
	 store_high <= high_in;
      end
   end

   internal int1
     (
      .d_in (store_high),
      .d_out (tmp_h)
      );

   internal int2
     (
      .d_in (tmp_h),
      .d_out (sink_h)
      );
      
   internal int3
     (
      .d_in (store_low),
      .d_out(tmp_l)
      );

   internal int4
     (
      .d_in (tmp_l),
      .d_out(sink_l)
      );
   
endmodule
