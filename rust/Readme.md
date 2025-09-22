# Absurd Algebra - Rust Implementation

[![Crates.io](https://img.shields.io/crates/v/absurd-algebra.svg)](https://crates.io/crates/absurd-algebra)
[![Documentation](https://docs.rs/absurd-algebra/badge.svg)](https://docs.rs/absurd-algebra)

<p align="center">
  <a href="https://doi.org/10.5281/zenodo.15713199">📄 Research Paper</a>
</p>

A Rust implementation of **Absurd Algebra**, a mathematical framework that extends traditional field theory to allow division by zero in an algebraically consistent manner.

---

## Overview

Absurd Algebra introduces **Absurd Numbers** of the form

```
a + bz
```

where:
- \(a, b\) are complex numbers  
- \(z = 1/0\) is the "absurd unit", the multiplicative inverse of zero  

Within this framework, division by zero becomes meaningful:
```
x / 0 = x * z
```

---

## Installation

Add the following to your `Cargo.toml`:

```toml
[dependencies]
num-absurd = "0.1.0"
num-complex = "0.4.6"
```

or run following command in your project directory:

```sh
cargo add num-absurd
```

--- 

## Usage Example

```
use num_absurd::*;

fn main() {
    // Complex numbers via co! macro
    let c1 = co!(1.0, 2.0);    // 1 + 2i
    let c2 = co!(3.0);         // 3 + 0i

    // Absurd numbers via ab! macro
    let a1 = ab!(co!(1.0, 2.0), co!(3.0, 0.0));  // (1+2i) + 3z
    let a2 = ab!(co!(0.0, 1.0), co!(1.0, 0.0));  // i + z
    
    // Real-coefficient shorthand
    let a3 = ab_real!(2.0, 1.0);  // 2 + z

    // Division by zero
    let two = ab_real!(2.0, 0.0);     
    let result = two.divide_by_zero(); // 2z
    println!("2/0 = {}", result);

    // Arithmetic
    let sum = a1 + a2;
    let difference = a1 - a2;
    let product = a1 * a2;
    let quotient = a1 / a2;

    // Absurd unit
    let z = Absurd::<f64>::z(); 
    println!("Absurd unit: {}", z); // z

    // Conjugates
    let complex_conj = a1.complex_conjugate(); 
    let absurd_conj = a1.absurd_conjugate();

    // Norms
    let norm = a1.norm();            
    let norm_sq = a1.norm_squared(); 
}
```

## Documentation

- API Reference: [docs.rs/num-absurd](https://docs.rs/num-absurd)
- Complex Numbers: [docs.rs/num-complex](https://docs.rs/num-complex)

## License

This project is licensed under the MIT License. See the [LICENSE](../LICENSE) file for details.
