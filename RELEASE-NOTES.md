## 0.19.1

### Features

* New errors for the following constant simplification scenarios (see #1191):
  1. Division by 0
  1. Mod (%) by 0
  1. Negative expoents
  1. Expoents bigger than an Integer
  1. Expoential operations that would overflow `BigInt`
