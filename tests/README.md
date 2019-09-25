# Benchmarks for Word-level Model Checking

Compiled by Aman Goel [(amangoel@umich.edu)](amangoel@umich.edu)  and  Karem A. Sakallah [(karem@umich.edu)](karem@umich.edu) , University of Michigan


#### Description
535 invariant checking problems (Verilog RTL files with SystemVerilog assertions, as well as in BTOR2 format) that can be classified as follows:

- **opensource:** 
A set of 141 problems collected from benchmark suites accompanying tools vcegar [1] (#23), v2c [2] (#32) and verilog2smv [3] (#86). Problems include cores from picoJava, USB 1.1, CRC generation, Huffman coding, mutual exclusion algorithms, simple microprocessor, etc.

- **industry:** 
A set of 370 problems collected from industrial collaborators. Of these, 124 were categorized as easy (named gen\*) (code sizes between 155 and 761 lines; # of flip-flops between 514 and 931), and 235 as challenging (named cal\*) (code sizes between 109 and 22065 lines; # of flip-flops between 6 and 7249). The remaining 11 problems (named mul\*) involved sequential equivalence checking on a multiplier design before and after clock gating optimization.

- **crafted:** 
A set of 24 simple problems synthetically created for calibration (includes both control- and data-centric problems) [4].


#### References
1. Jain, H., Kroening, D., Sharygina, N. and Clarke, E., 2007, March. VCEGAR: Verilog counterexample guided abstraction refinement. In International Conference on Tools and Algorithms for the Construction and Analysis of Systems (pp. 583-586). Springer, Berlin, Heidelberg.

2. Mukherjee, R., Tautschnig, M. and Kroening, D., 2016, April. v2c–A verilog to C translator. In International Conference on Tools and Algorithms for the Construction and Analysis of Systems (pp. 580-586). Springer, Berlin, Heidelberg.

3. Irfan, A., Cimatti, A., Griggio, A., Roveri, M. and Sebastiani, R., 2016, March. Verilog2SMV: a tool for word-level verification. In Proceedings of the 2016 Conference on Design, Automation & Test in Europe (pp. 1156-1159). EDA Consortium.

4. https://github.com/aman-goel/verilogbench

Please report any corrections or usage experience via email  [(amangoel@umich.edu)](amangoel@umich.edu) or on github [(https://github.com/aman-goel/avr)](https://github.com/aman-goel/avr)
