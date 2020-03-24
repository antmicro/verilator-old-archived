module t (/*AUTOARG*/
   // Inputs
   clk
   );
   input clk;

   string test_string = "abcd";

   int array3d[2][3][4] = '{
                             '{
                                '{  0,  1,  2,  3},
                                '{  4,  5,  6,  7},
                                '{  8,  9, 10, 11}
                              },
                             '{
                                '{ 12, 13, 14, 15},
                                '{ 16, 17, 18, 19},
                                '{ 20, 21, 22, 23}
                              }
                           };
   int pos;
   int val;
   byte b;

   initial begin

      pos = 3;
      b = test_string[--pos];
      if (b !== "c") $stop;
      if (pos !== 2) $stop;

      pos = 0;
      b = test_string[++pos];
      if (b !== "b") $stop;
      if (pos !== 1) $stop;

      pos = 3;
      b = test_string[pos--];
      if (b !== "d") $stop;
      if (pos !== 3) $stop;

      pos = 0;
      b = test_string[pos++];
      if (b !== "a") $stop;
      if (pos !== 1) $stop;

      pos = 0;
      val = array3d[pos++][pos++][++pos];
      if (val !== 7) $stop;
      if (pos !== 3) $stop;

      pos = 0;
      val = 0 & array3d[0][0][++pos];
      if (val != 1) $stop;
      if (pos != 1) $stop;

      pos = 0;
      val = 0 && array3d[0][0][++pos];
      if (val != 0) $stop;
      if (pos != 0) $stop;

      $write("*-* All Finished *-*\n");
      $finish;

   end
endmodule
