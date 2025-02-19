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


   always@(posedge clk) begin
      if (cond) begin
	 store_implicit <= store_high;
      end else begin
	 store_implicit <= store_low;
      end
   end

   assign sink = store_implicit; //error, store_implicit assumed {H}
   
endmodule
