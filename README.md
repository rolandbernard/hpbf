# High-performance Brainfuck

This is a fast virtual machine for Brainfuck.

## How fast is it?

| Flags                 | `mandel.bf` | `hanoi.bf` | `factor.bf` | `dbfi.bf^2(hello.bf)` |
|-----------------------|-------------|------------|-------------|-----------------------|
| `--inplace`           |     17.272s |    10.162s |    235.852s |               89.494s |
| `--ir-int -O0`        |      5.959s |      826ms |    132.505s |               84.820s |
| `--ir-int -O1`        |      6.282s |       32ms |     51.007s |               86.448s |
| `--ir-int -O3`        |      6.381s |       34ms |     51.062s |               84.531s |
| `--bc-int -O0`        |      2.053s |      175ms |     35.887s |               21.004s |
| `--bc-int -O1`        |      1.423s |       18ms |     11.848s |               20.809s |
| `--bc-int -O3`        |      1.413s |       21ms |     11.731s |               20.764s |
| `--bc-int --static`   |      1.310s |       19ms |     11.761s |               15.409s |
| `--llvm-jit -O0`      |      9.245s |      315ms |     55.432s |              272.589s |
| `--llvm-jit -O1`      |      1.158s |      276ms |      4.292s |               18.345s |
| `--llvm-jit -O2`      |      1.173s |      246ms |      4.294s |               18.305s |
| `--llvm-jit -O3`      |      1.222s |      379ms |      4.351s |               18.486s |
| `--llvm-jit -O4`      |      1.481s |      571ms |      3.700s |               18.719s |
| `--llvm-jit -O5`      |      1.472s |      573ms |      3.689s |               18.789s |
| `--llvm-jit --static` |       693ms |      237ms |      3.442s |               11.338s |
| `--base-jit -O0`      |      1.146s |      108ms |     16.331s |               18.880s |
| `--base-jit -O1`      |       796ms |       13ms |      3.508s |               19.193s |
| `--base-jit -O3`      |       843ms |       17ms |      3.501s |               19.257s |
| `--base-jit --static` |       512ms |       16ms |      3.057s |               10.336s |

./target/release/hpbf --time -f examples/mandel.bf <Flags>
./target/release/hpbf --time -f examples/hanoi.bf <Flags>
./target/release/hpbf --time -f examples/factor.bf <Flags> <<< "87178291199"
cat examples/dbfi.bf examples/input.bf examples/hello.bf examples/input.bf | ./target/release/hpbf --time -f examples/dbfi.bf <Flags>

## How does it work?


