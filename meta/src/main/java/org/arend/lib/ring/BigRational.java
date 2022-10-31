package org.arend.lib.ring;

import java.math.BigInteger;

public class BigRational implements Ring {
  public final BigInteger nom;
  public final BigInteger denom;

  public final static BigRational ZERO = new BigRational(BigInteger.ZERO, BigInteger.ONE);
  public final static BigRational ONE = new BigRational(BigInteger.ONE, BigInteger.ONE);

  private BigRational(BigInteger nom, BigInteger denom) {
    this.nom = nom;
    this.denom = denom;
  }

  public static BigRational make(BigInteger nom, BigInteger denom) {
    BigInteger gcd = nom.gcd(denom);
    return new BigRational(nom.divide(gcd), denom.divide(gcd));
  }

  public static BigRational makeInt(BigInteger nom) {
    return new BigRational(nom, BigInteger.ONE);
  }

  @Override
  public BigRational add(Ring x) {
    return BigRational.make(nom.multiply(((BigRational) x).denom).add(((BigRational) x).nom.multiply(denom)), denom.multiply(((BigRational) x).denom));
  }

  @Override
  public BigRational multiply(Ring x) {
    return BigRational.make(nom.multiply(((BigRational) x).nom), denom.multiply(((BigRational) x).denom));
  }

  @Override
  public BigRational negate() {
    return new BigRational(nom.negate(), denom);
  }

  @Override
  public BigRational subtract(Ring x) {
    return BigRational.make(nom.multiply(((BigRational) x).denom).subtract(((BigRational) x).nom.multiply(denom)), denom.multiply(((BigRational) x).denom));
  }
}