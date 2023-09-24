package org.example;

import java.math.BigInteger;
import java.util.Arrays;

public class AKS {

    /**
     * вычислить НОД методом Евклида
     */
    public static BigInteger gcd(BigInteger a, BigInteger b) {
        if (b.equals(BigInteger.ZERO)) {
            return a;
        }
        return gcd(b, a.mod(b));
    }

    public static long ordr(long r, BigInteger n) {
        for (int i = 1; ; i++) {
            BigInteger mod = n.pow(i).mod(BigInteger.valueOf(r));
            if (mod.equals(BigInteger.ONE)) {
                return i;
            }
        }
    }

    /**
     * найти наименьшее r такое что ord(r, n) > (log2 n)^2
     */
    public static long findSmallestR(BigInteger n) {
        long log2n = n.bitLength();
        log2n *= log2n;
        long r = 2;
        while (true) {
            if (gcd(BigInteger.valueOf(r), n).equals(BigInteger.ONE) && ordr(r, n) > log2n) {
                return r;
            }
            r++;
        }
    }

    /**
     * вычислить функцию Эйлера
     */
    public static long phi(BigInteger n) {
        long count = 0;
        for (BigInteger i = BigInteger.ONE; i.compareTo(n) < 0; i = i.add(BigInteger.ONE)) {
            if (gcd(i, n).equals(BigInteger.ONE)) {
                count++;
            }
        }
        return count;
    }

    /**
     * перемножение двух многочленов
     */
    public static BigInteger[] convolve(BigInteger[] volume, BigInteger[] kernel) {
        int volumeLength = volume.length;
        int kernelLength = kernel.length;

        if (volumeLength == 0 || kernelLength == 0) {
            return new BigInteger[0];
        }

        int displacement = 0;
        BigInteger[] convArr = new BigInteger[volumeLength + kernelLength - 1];
        Arrays.fill(convArr, BigInteger.ZERO);

        for (int i = 0; i < volumeLength; i++) {
            for (int j = 0; j < kernelLength; j++) {
                if (displacement + j < convArr.length) {
                    BigInteger mul = volume[i].multiply(kernel[j]);
                    convArr[displacement + j] = convArr[displacement + j].add(mul);
                }
            }
            displacement++;
        }

        return convArr;
    }

    /**
     * остаток от деления многочлена на n
     */
    public static BigInteger[] modN(BigInteger[] arr, BigInteger n) {
        BigInteger[] modArr = new BigInteger[arr.length];
        for (int i = 0; i < arr.length; i++) {
            modArr[i] = arr[i].mod(n);
        }
        return modArr;
    }

    /**
     * вычисляет массив полиномиальных коэффициентов для (x + a)^n (mod n)
     */
    public static BigInteger[] polyModN(long a, BigInteger n) {
        BigInteger[] x = {BigInteger.valueOf(a), BigInteger.ONE};
        BigInteger[] res = {BigInteger.ONE};
        BigInteger counter = n;
        while (counter.compareTo(BigInteger.ZERO) > 0) {
            if (counter.mod(BigInteger.TWO).equals(BigInteger.ONE)) {
                res = convolve(res, x);
                res = modN(res, n);
            }
            x = convolve(x, x);
            x = modN(x, n);
            counter = counter.divide(BigInteger.TWO);
        }
        return res;
    }

    /**
     * Вычисляет остаток от деления заданного полинома
     * (x + a)^n (mod x^r - 1).
     */
    public static BigInteger[] polyRemainder(BigInteger[] poly, int r) {
        BigInteger[] remainder = new BigInteger[r];
        Arrays.fill(remainder, BigInteger.ZERO);
        for (int i = 0; i < poly.length; i++) {
            if (i < r) {
                remainder[i] = poly[i];
            } else {
                remainder[i % r] = remainder[i % r].add(poly[i]);
            }
        }
        return remainder;
    }

    /**
     * Для данного целого числа a проверяет остаток от деления полинома
     * (x + a)^n  = (x^n + a) [mod (x^r - 1), n],
     */
    public static boolean checkPolyMod(long a, BigInteger n, long r) {
        BigInteger[] poly = polyModN(a, n);
        BigInteger[] remainder = polyRemainder(poly, (int) r);
        int q = n.mod(BigInteger.valueOf(r)).intValue();
        remainder[q] = remainder[q].subtract(BigInteger.ONE);
        remainder[0] = remainder[0].subtract(BigInteger.valueOf(a));
        for (BigInteger t : remainder) {
            if (!t.mod(n).equals(BigInteger.ZERO)) {
                return false;
            }
        }
        return true;
    }

    public static boolean binarySearchTestB(int b, BigInteger n) {
        BigInteger upperBoundA = BigInteger.ONE;
        while (upperBoundA.pow(b).compareTo(n) < 0) {
            upperBoundA = upperBoundA.multiply(BigInteger.TWO);
        }
        BigInteger dx = upperBoundA.divide(BigInteger.TWO);
        while (dx.compareTo(BigInteger.ZERO) > 0) {
            if (upperBoundA.pow(b).compareTo(n) == 0) {
                return true;
            }
            if (upperBoundA.subtract(dx).pow(b).compareTo(n) > -1) {
                upperBoundA = upperBoundA.subtract(dx);
            }
            dx = dx.divide(BigInteger.TWO);
        }
        return false;
    }

    public static boolean checkIfPrime(BigInteger n) {
        if (n.compareTo(BigInteger.TWO) < 0) {
            throw new IllegalArgumentException("число должно быть не меньше 2");
        }

        /**
         * шаг 1, проверяем что n = a^b где a > 1 and b > 1
         */

        int upperBoundB = n.bitLength();
        for (int b = 2; b <= upperBoundB; b++) {
            if (binarySearchTestB(b, n)) {
                return false;
            }
        }


        /**
         * шаг 2, находим наименьшее r такое что odr(n) > (log2 n)^2
         */
        long r = findSmallestR(n);

        /**
         * шаг 3, если 1 < нод(a, n) < n для каждого a <= r, n - составное.
         */
        for (long a = r; a > 1; a--) {
            BigInteger gcd = gcd(BigInteger.valueOf(a), n);
            if (BigInteger.ONE.compareTo(gcd) < 0 && gcd.compareTo(n) < 0) {
                return false;
            }
        }

        /**
         * шаг 4, если n <= r, n - простое.
         */
        if (n.compareTo(BigInteger.valueOf(r)) < 1) {
            return true;
        }

        /**
         * шаг 5, проверяем что
         * для каждого a от 1 до [floor(sqrt(phi(n)) * log(n))]
         * if (x + a)^n != x^n + a (mod x^r - 1, n) n - составное
         */
        long max = (long) (Math.floor(Math.sqrt(phi(BigInteger.valueOf(r))) * n.bitLength()));
        for (int a = 1; a <= max; a++) {
            System.out.print("a= " + a + "/" + max);
            if (!checkPolyMod(a, n, r)) {
                return false;
            }
            System.out.print("\r");
        }

        /**
         * шаг 6, n - простое
         */
        return true;
    }

    public static void main(String[] args) {
        long number = 773;
        boolean isPrime = checkIfPrime(BigInteger.valueOf(number));
        System.out.println(isPrime ? number + " is prime" : number + " is not prime");
    }
}
