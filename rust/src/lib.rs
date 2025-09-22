use std::ops::{Add, Sub, Mul, Div, Neg};
use std::fmt::{Display, Debug, Formatter, Result as FmtResult};
use num_complex::Complex;
use num_traits::{Zero, One, Float};

/// Macro for creating complex numbers with real and imaginary parts
///
/// # Examples
///
/// ```rust
/// # use num_absurd::co;
/// let c1 = co!(1.0, 2.0);    // 1 + 2i
/// let c2 = co!(3.0);         // 3 + 0i (real number)
/// ```
#[macro_export]
macro_rules! co {
    ($re:expr, $im:expr) => {
        Complex::new($re, $im)
    };
    ($re:expr) => {
        Complex::new($re, <_ as num_traits::Zero>::zero())
    };
}

/// Macro for creating absurd numbers with complex and absurd parts
///
/// # Examples
///
/// ```rust
/// # use num_absurd::{ab, co};
/// let a1 = ab!(co!(1.0, 0.0), co!(2.0, 0.0));  // 1 + 2z
/// let a2 = ab!(co!(0.0, 1.0), co!(1.0, 0.0));  // i + z
/// let a3 = ab_real!(1.0, 2.0);                  // 1 + 2z (shorthand for reals)
/// ```
#[macro_export]
macro_rules! ab {
    // Match when both arguments are complex numbers (contain co! or Complex::new)
    ($co:expr, $ab:expr) => {
        Absurd::new($co, $ab)
    };
}

/// Macro for creating absurd numbers from real number components
///
/// # Examples
///
/// ```rust
/// # use num_absurd::ab_real;
/// let a = ab_real!(1.0, 2.0);  // 1 + 2z (both parts are real)
/// ```
#[macro_export]
macro_rules! ab_real {
    ($co_re:expr, $ab_re:expr) => {
        Absurd::new(co!($co_re), co!($ab_re))
    };
}

/// An Absurd Number representing `a + bz` where `a, b` are complex numbers
/// and `z = 1/0` is the absurd unit.
///
/// # Type Parameters
///
/// * `T` - The underlying numeric type (must implement `Float + Clone + Debug`)
///
/// # Mathematical Foundation
///
/// Absurd numbers extend complex numbers by introducing the absurd unit `z = 1/0`.
/// This allows division by zero to be defined consistently within the algebraic structure.
///
/// ## Representation
///
/// An absurd number has the form: `(a + bi) + (c + di)z`
/// where:
/// - `a, b, c, d ∈ ℝ` (real numbers)
/// - `i` is the imaginary unit (`i² = -1`)
/// - `z` is the absurd unit (`z = 1/0`)
///
/// # Examples
///
/// ```rust
/// use num_absurd::*;
///
/// // Create absurd numbers
/// let a1: Absurd<f64> = ab!(co!(1.0, 2.0), co!(3.0, 0.0));  // (1+2i) + 3z
/// let a2: Absurd<f32> = ab!(2.0, 1.0);                       // 2 + z
///
/// // Arithmetic operations
/// let sum = a1 + a1;
/// let difference = a1 - a2;
/// ```
#[derive(Debug, Clone, PartialEq)]
pub struct Absurd<T>
where
    T: Float + Clone + Debug,
{
    /// The complex part (coefficient of 1)
    pub complex: Complex<T>,
    /// The absurd part (coefficient of z)
    pub absurd: Complex<T>,
}

impl<T> Absurd<T>
where
    T: Float + Clone + Debug,
{
    /// Create a new absurd number from complex and absurd parts
    ///
    /// # Arguments
    ///
    /// * `complex` - The complex coefficient (coefficient of 1)
    /// * `absurd` - The absurd coefficient (coefficient of z)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = Absurd::new(co!(1.0, 2.0), co!(3.0, 0.0));  // (1+2i) + 3z
    /// ```
    pub fn new(complex: Complex<T>, absurd: Complex<T>) -> Self {
        Self { complex, absurd }
    }

    /// Create an absurd number from real parts only
    ///
    /// # Arguments
    ///
    /// * `complex_re` - Real part of complex coefficient
    /// * `absurd_re` - Real part of absurd coefficient
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = Absurd::from_reals(1.0, 2.0);  // 1 + 2z
    /// // Or use the macro: ab_real!(1.0, 2.0)
    /// ```
    pub fn from_reals(complex_re: T, absurd_re: T) -> Self {
        Self {
            complex: Complex::new(complex_re, T::zero()),
            absurd: Complex::new(absurd_re, T::zero()),
        }
    }

    /// Create a pure complex absurd number (absurd part is zero)
    ///
    /// # Arguments
    ///
    /// * `complex` - The complex number
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = Absurd::from_complex(co!(1.0, 2.0));  // (1+2i) + 0z
    /// ```
    pub fn from_complex(complex: Complex<T>) -> Self {
        Self {
            complex,
            absurd: Complex::zero(),
        }
    }

    /// Create a pure absurd number (complex part is zero)
    ///
    /// # Arguments
    ///
    /// * `absurd` - The absurd coefficient
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = Absurd::from_absurd(co!(1.0, 2.0));  // 0 + (1+2i)z
    /// ```
    pub fn from_absurd(absurd: Complex<T>) -> Self {
        Self {
            complex: Complex::zero(),
            absurd,
        }
    }

    /// Get the absurd unit `z = 1/0`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let z: Absurd<f64> = Absurd::z();  // 0 + 1z
    /// ```
    pub fn z() -> Self {
        Self {
            complex: Complex::zero(),
            absurd: Complex::one(),
        }
    }

    /// Check if this is a pure complex number (absurd part is zero)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a1 = ab!(co!(1.0, 2.0), co!(0.0, 0.0));
    /// let a2 = ab!(co!(1.0, 2.0), co!(1.0, 0.0));
    ///
    /// assert!(a1.is_complex());
    /// assert!(!a2.is_complex());
    /// ```
    pub fn is_complex(&self) -> bool {
        self.absurd.is_zero()
    }

    /// Check if this is a pure absurd number (complex part is zero)
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a1 = ab!(co!(0.0, 0.0), co!(1.0, 2.0));
    /// let a2 = ab!(co!(1.0, 0.0), co!(1.0, 2.0));
    ///
    /// assert!(a1.is_pure_absurd());
    /// assert!(!a2.is_pure_absurd());
    /// ```
    pub fn is_pure_absurd(&self) -> bool {
        self.complex.is_zero()
    }

    /// Attempt to convert to a complex number if absurd part is zero
    ///
    /// # Returns
    ///
    /// `Some(complex)` if absurd part is zero, `None` otherwise
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a1 = ab!(co!(1.0, 2.0), co!(0.0, 0.0));
    /// let a2 = ab!(co!(1.0, 2.0), co!(1.0, 0.0));
    ///
    /// assert!(a1.to_complex().is_some());
    /// assert!(a2.to_complex().is_none());
    /// ```
    pub fn to_complex(&self) -> Option<Complex<T>> {
        if self.is_complex() {
            Some(self.complex)
        } else {
            None
        }
    }

    /// Multiply by the absurd unit (equivalent to dividing by zero)
    ///
    /// For any absurd number `a + bz`, multiplying by `z` gives:
    /// `(a + bz) * z = az + b`
    ///
    /// This effectively "shifts" the complex part to the absurd part
    /// and reduces the absurd part by one power of z.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(1.0, 2.0), co!(3.0, 0.0));  // (1+2i) + 3z
    /// let result = a.multiply_by_z();              // (1+2i)z + 3
    /// ```
    pub fn multiply_by_z(&self) -> Self {
        Self {
            complex: self.absurd,
            absurd: self.complex,
        }
    }

    /// Divide by zero (equivalent to multiplying by the absurd unit)
    ///
    /// This is an alias for `multiply_by_z()` that makes the operation
    /// more explicit in terms of division by zero.
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(2.0, 0.0), co!(0.0, 0.0));  // 2 + 0z
    /// let result = a.divide_by_zero();             // 0 + 2z (which is 2z)
    /// ```
    pub fn divide_by_zero(&self) -> Self {
        self.multiply_by_z()
    }

    /// Get the complex conjugate of the absurd number
    ///
    /// For an absurd number `(a + bi) + (c + di)z`, the complex conjugate is:
    /// `(a - bi) + (c - di)z`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
    /// let conj = a.complex_conjugate();
    /// // conj = (1-2i) + (3-4i)z
    /// ```
    pub fn complex_conjugate(&self) -> Self {
        Self {
            complex: self.complex.conj(),
            absurd: self.absurd.conj(),
        }
    }

    /// Get the absurd conjugate of the absurd number
    ///
    /// For an absurd number `a + bz`, the absurd conjugate is: `a - bz`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
    /// let conj = a.absurd_conjugate();
    /// // conj = (1+2i) - (3+4i)z
    /// ```
    pub fn absurd_conjugate(&self) -> Self {
        Self {
            complex: self.complex,
            absurd: -self.absurd,
        }
    }

    /// Calculate the norm squared of the absurd number
    ///
    /// For `a + bz`, this returns `|a|² + |b|²`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(3.0, 4.0), co!(1.0, 2.0));
    /// let norm_sq = a.norm_squared();
    /// // |3+4i|² + |1+2i|² = 25 + 5 = 30
    /// ```
    pub fn norm_squared(&self) -> T {
        self.complex.norm_sqr() + self.absurd.norm_sqr()
    }

    /// Calculate the norm of the absurd number
    ///
    /// For `a + bz`, this returns `√(|a|² + |b|²)`
    ///
    /// # Examples
    ///
    /// ```rust
    /// use num_absurd::*;
    ///
    /// let a = ab!(co!(3.0, 4.0), co!(0.0, 0.0));
    /// let norm = a.norm();
    /// // √(|3+4i|²) = √25 = 5
    /// ```
    pub fn norm(&self) -> T {
        self.norm_squared().sqrt()
    }
}

// Implement Zero trait
impl<T> Zero for Absurd<T>
where
    T: Float + Clone + Debug,
{
    fn zero() -> Self {
        Self {
            complex: Complex::zero(),
            absurd: Complex::zero(),
        }
    }

    fn is_zero(&self) -> bool {
        self.complex.is_zero() && self.absurd.is_zero()
    }
}

// Implement One trait
impl<T> One for Absurd<T>
where
    T: Float + Clone + Debug,
{
    fn one() -> Self {
        Self {
            complex: Complex::one(),
            absurd: Complex::zero(),
        }
    }
}

// Addition: (a₁ + b₁z) + (a₂ + b₂z) = (a₁ + a₂) + (b₁ + b₂)z
impl<T> Add for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn add(self, rhs: Self) -> Self::Output {
        Self {
            complex: self.complex + rhs.complex,
            absurd: self.absurd + rhs.absurd,
        }
    }
}

// Subtraction: (a₁ + b₁z) - (a₂ + b₂z) = (a₁ - a₂) + (b₁ - b₂)z
impl<T> Sub for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn sub(self, rhs: Self) -> Self::Output {
        Self {
            complex: self.complex - rhs.complex,
            absurd: self.absurd - rhs.absurd,
        }
    }
}

// Negation: -(a + bz) = -a + (-b)z
impl<T> Neg for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn neg(self) -> Self::Output {
        Self {
            complex: -self.complex,
            absurd: -self.absurd,
        }
    }
}

// Multiplication: (a₁ + b₁z)(a₂ + b₂z) = a₁a₂ + (a₁b₂ + a₂b₁)z + b₁b₂z²
// Since z² behavior follows polynomial ring rules, we need special handling
impl<T> Mul for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn mul(self, rhs: Self) -> Self::Output {
        // For now, implement basic multiplication
        // More complex z² handling can be added later
        let complex_part = self.complex * rhs.complex;
        let absurd_part = self.complex * rhs.absurd + self.absurd * rhs.complex;
        
        Self {
            complex: complex_part,
            absurd: absurd_part,
        }
    }
}

// Scalar multiplication
impl<T> Mul<T> for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn mul(self, rhs: T) -> Self::Output {
        Self {
            complex: self.complex * rhs,
            absurd: self.absurd * rhs,
        }
    }
}

// Division implementation
impl<T> Div for Absurd<T>
where
    T: Float + Clone + Debug,
{
    type Output = Self;

    fn div(self, rhs: Self) -> Self::Output {
        if rhs.is_zero() {
            // Division by zero: multiply by z
            self.multiply_by_z()
        } else {
            // Standard division for non-zero denominators
            // This is a simplified implementation
            let norm_sq = rhs.norm_squared();
            let conj = rhs.complex_conjugate();
            let numerator = self * conj;
            
            Self {
                complex: numerator.complex / norm_sq,
                absurd: numerator.absurd / norm_sq,
            }
        }
    }
}

// Display implementation
impl<T> Display for Absurd<T>
where
    T: Float + Clone + Debug + Display,
{
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        let complex_zero = Complex::zero();
        let absurd_zero = Complex::zero();

        if self.complex == complex_zero && self.absurd == absurd_zero {
            write!(f, "0")
        } else if self.absurd == absurd_zero {
            write!(f, "{}", self.complex)
        } else if self.complex == complex_zero {
            if self.absurd == Complex::one() {
                write!(f, "z")
            } else {
                write!(f, "{}z", self.absurd)
            }
        } else {
            if self.absurd == Complex::one() {
                write!(f, "{} + z", self.complex)
            } else {
                write!(f, "{} + {}z", self.complex, self.absurd)
            }
        }
    }
}

// Convenient type aliases
/// 32-bit floating point absurd number
pub type Absurd32 = Absurd<f32>;

/// 64-bit floating point absurd number  
pub type Absurd64 = Absurd<f64>;

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_creation() {
        let a1 = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        assert_eq!(a1.complex, co!(1.0, 2.0));
        assert_eq!(a1.absurd, co!(3.0, 4.0));
    }

    #[test]
    fn test_addition() {
        let a1 = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        let a2 = ab!(co!(5.0, 6.0), co!(7.0, 8.0));
        let result = a1 + a2;
        
        assert_eq!(result.complex, co!(6.0, 8.0));
        assert_eq!(result.absurd, co!(10.0, 12.0));
    }

    #[test]
    fn test_multiplication() {
        let a1 = ab!(co!(1.0, 0.0), co!(0.0, 0.0));  // 1
        let a2 = ab!(co!(2.0, 0.0), co!(0.0, 0.0));  // 2
        let result = a1 * a2;
        
        assert_eq!(result.complex, co!(2.0, 0.0));
        assert_eq!(result.absurd, co!(0.0, 0.0));
    }

    #[test]
    fn test_division_by_zero() {
        let a = ab!(co!(2.0, 0.0), co!(0.0, 0.0));  // 2
        let zero = Absurd::<f64>::zero();
        let result = a / zero;
        
        // 2 / 0 should equal 2z
        assert_eq!(result.complex, co!(0.0, 0.0));
        assert_eq!(result.absurd, co!(2.0, 0.0));
    }

    #[test]
    fn test_absurd_unit() {
        let z = Absurd::<f64>::z();
        assert_eq!(z.complex, co!(0.0, 0.0));
        assert_eq!(z.absurd, co!(1.0, 0.0));
    }

    #[test]
    fn test_multiply_by_z() {
        let a = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        let result = a.multiply_by_z();
        
        // (1+2i) + (3+4i)z → (3+4i) + (1+2i)z
        assert_eq!(result.complex, co!(3.0, 4.0));
        assert_eq!(result.absurd, co!(1.0, 2.0));
    }

    #[test]
    fn test_conjugates() {
        let a = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        
        let complex_conj = a.complex_conjugate();
        assert_eq!(complex_conj.complex, co!(1.0, -2.0));
        assert_eq!(complex_conj.absurd, co!(3.0, -4.0));
        
        let absurd_conj = a.absurd_conjugate();
        assert_eq!(absurd_conj.complex, co!(1.0, 2.0));
        assert_eq!(absurd_conj.absurd, co!(-3.0, -4.0));
    }

    #[test]
    fn test_norm() {
        let a = ab!(co!(3.0, 4.0), co!(0.0, 0.0));  // 3+4i
        let norm = a.norm();
        assert!((norm - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_macros() {
        let c = co!(1.0, 2.0);
        assert_eq!(c, Complex::new(1.0, 2.0));
        
        let c_real = co!(3.0);
        assert_eq!(c_real, Complex::new(3.0, 0.0));
        
        let a = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        assert_eq!(a.complex, co!(1.0, 2.0));
        assert_eq!(a.absurd, co!(3.0, 4.0));
        
        let a_simple = ab_real!(1.0, 2.0);
        assert_eq!(a_simple.complex, co!(1.0, 0.0));
        assert_eq!(a_simple.absurd, co!(2.0, 0.0));
    }

    #[test]
    fn test_is_predicates() {
        let complex_only = ab!(co!(1.0, 2.0), co!(0.0, 0.0));
        let absurd_only = ab!(co!(0.0, 0.0), co!(1.0, 2.0));
        let mixed = ab!(co!(1.0, 2.0), co!(3.0, 4.0));
        
        assert!(complex_only.is_complex());
        assert!(!complex_only.is_pure_absurd());
        
        assert!(!absurd_only.is_complex());
        assert!(absurd_only.is_pure_absurd());
        
        assert!(!mixed.is_complex());
        assert!(!mixed.is_pure_absurd());
    }
}