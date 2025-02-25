`include "internal.vh"

module infer(
	     input {L} clk,
	     input cond,
	     input low_in,
	     input {H} high_in,
	     output {L} sink
	     );   

   reg	seq {L}	   store_low;
   reg	seq {H}	   store_high;
   reg	store_implicit; //should infer seq type

   wire	tmp_h; //should infer {H} type
   
   always@(posedge clk) begin
      if (cond) begin
	 store_low <= low_in;
      end else begin
	 store_low <= high_in; //error expected
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
      .d_in (store_implicit),
      .d_out (tmp_h)
      );

   internal int2
     (
      .d_in (tmp_h),
      .d_out(sink)
      );
   
   always@(posedge clk) begin
      if (cond) begin
	 store_implicit <= store_high;
      end else begin
	 store_implicit <= store_low;
      end
   end

//Expected constraints:
   //    store_high join store_cond <= store_implicit
   //    store_low  join store_cond <= store_implicit
   //    store_implicit <= d_in
   //    d_out <= tmp_h
   //    tmp_h <= d_in
   //    d_out <= sink
endmodule
