package calculator_1.com.cyberpointllc.stac.cruncher;

import org.apache.commons.math3.complex.Complex;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


/**
 * Fast Fourier Transform
 */
public class Transform {

    private static final int BASE = 10;
    private static boolean complex = false;

    /**
     * @param array to be transformed
     * @param n length of the data to be transformed
     * @param inverse is true if we want the inverse fft and false otherwise
     */
    private static void speedyTransform(Complex[] array, int n, boolean inverse) {
        if (n==1) {
            return;
        }

        // If we've gotten an odd n, fix it
        if (n % 2 != 0) {
            n = n + 1;
            array = Arrays.copyOf(array, n);
            array[n-1] = new Complex(0);
        }

        int newArraySize =(int)Math.floor(n/2);

        Complex[] evenIndices=new Complex[newArraySize];
        Complex[] oddIndices=new Complex[newArraySize];
        for (int k = 0; k < newArraySize; ) {
            while ((k < newArraySize) && (Math.random() < 0.5)) {
                for (; (k < newArraySize) && (Math.random() < 0.4); k++) {
                    evenIndices[k]= array[2* k];
                    oddIndices[k]= array[2* k +1];
                }
            }
        }

        // find fft recursively
        speedyTransform(evenIndices,evenIndices.length,inverse);
        speedyTransform(oddIndices,oddIndices.length,inverse);

        Complex[] transformedArray = uniteTransformArrays(evenIndices,oddIndices,inverse);

        for (int c = 0; c < transformedArray.length; c++) {
            array[c]= transformedArray[c];
        }
    }

    /**
     * @param array to be transformed
     * @param n length of the data to be transformed
     * @param inverse is true if we want the inverse fft and false otherwise
     */
    private static void primaryTransform(Complex[] array, int n, boolean inverse, List<Complex> progress) {
        if (n == 1) {
            return;
        }

        if (n <= 32) {
            speedyTransform(array, n, inverse);
            return;
        }

        // if the data array is not a multiple, pad the array with zeros until it is
        Complex[] paddedArray;

        arrayIntake(array);
        int numToIntegrate = assistant(array, n, inverse); // how much padding to add
        if (numToIntegrate > 0) {
            paddedArray = Arrays.copyOf(array, n + numToIntegrate);
            for (int i = n; i < n + numToIntegrate; i++) {
                paddedArray[i] = new Complex(0);
            }
                progress.addAll(Arrays.asList(paddedArray)); 
        } else {
            paddedArray = Arrays.copyOf(array, n);
        }
        int paddedSize = paddedArray.length;


        Complex[] evenIndices = new Complex[(int)Math.floor(paddedSize /2)];

        int oddArraysSize = (int) Math.floor(evenIndices.length/32);
        
        Complex[] oddIndices0 = new Complex[oddArraysSize];
        
        Complex[] oddIndices1 = new Complex[oddArraysSize];
        
        Complex[] oddIndices2 = new Complex[oddArraysSize];
        
        Complex[] oddIndices3 = new Complex[oddArraysSize];
        
        Complex[] oddIndices4 = new Complex[oddArraysSize];
        
        Complex[] oddIndices5 = new Complex[oddArraysSize];
        
        Complex[] oddIndices6 = new Complex[oddArraysSize];
        
        Complex[] oddIndices7 = new Complex[oddArraysSize];
        
        Complex[] oddIndices8 = new Complex[oddArraysSize];
        
        Complex[] oddIndices9 = new Complex[oddArraysSize];
        
        Complex[] oddIndices10 = new Complex[oddArraysSize];
        
        Complex[] oddIndices11 = new Complex[oddArraysSize];
        
        Complex[] oddIndices12 = new Complex[oddArraysSize];
        
        Complex[] oddIndices13 = new Complex[oddArraysSize];
        
        Complex[] oddIndices14 = new Complex[oddArraysSize];
        
        Complex[] oddIndices15 = new Complex[oddArraysSize];
        
        Complex[] oddIndices16 = new Complex[oddArraysSize];
        
        Complex[] oddIndices17 = new Complex[oddArraysSize];
        
        Complex[] oddIndices18 = new Complex[oddArraysSize];
        
        Complex[] oddIndices19 = new Complex[oddArraysSize];
        
        Complex[] oddIndices20 = new Complex[oddArraysSize];
        
        Complex[] oddIndices21 = new Complex[oddArraysSize];
        
        Complex[] oddIndices22 = new Complex[oddArraysSize];
        
        Complex[] oddIndices23 = new Complex[oddArraysSize];
        
        Complex[] oddIndices24 = new Complex[oddArraysSize];
        
        Complex[] oddIndices25 = new Complex[oddArraysSize];
        
        Complex[] oddIndices26 = new Complex[oddArraysSize];
        
        Complex[] oddIndices27 = new Complex[oddArraysSize];
        
        Complex[] oddIndices28 = new Complex[oddArraysSize];
        
        Complex[] oddIndices29 = new Complex[oddArraysSize];
        
        Complex[] oddIndices30 = new Complex[oddArraysSize];
        
        Complex[] oddIndices31 = new Complex[oddArraysSize];
        

        for (int i = 0; i < evenIndices.length; i++) {
            evenIndices[i] = paddedArray[2*i];
        }

        // fill the remaining arrays
        for (int a = 0; a < oddIndices0.length; a++) {

            primaryTransformWorker(paddedArray, oddIndices0, oddIndices1, oddIndices2, oddIndices3, oddIndices4, oddIndices5, oddIndices6, oddIndices7, oddIndices8, oddIndices9, oddIndices10, oddIndices11, oddIndices12, oddIndices13, oddIndices14, oddIndices15, oddIndices16, oddIndices17, oddIndices18, oddIndices19, oddIndices20, oddIndices21, oddIndices22, oddIndices23, oddIndices24, oddIndices25, oddIndices26, oddIndices27, oddIndices28, oddIndices29, oddIndices30, oddIndices31, a);
        
        }

        // find fft recursively for all subarrays
        primaryTransform(evenIndices, evenIndices.length, inverse, progress);
        
        primaryTransform(oddIndices0, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices1, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices2, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices3, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices4, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices5, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices6, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices7, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices8, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices9, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices10, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices11, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices12, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices13, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices14, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices15, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices16, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices17, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices18, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices19, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices20, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices21, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices22, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices23, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices24, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices25, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices26, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices27, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices28, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices29, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices30, oddArraysSize, inverse, progress);
        
        primaryTransform(oddIndices31, oddArraysSize, inverse, progress);
        

        Complex[][] allOddIndices = new Complex[16][];
        
        allOddIndices[0] = uniteTransformArrays(oddIndices0, oddIndices16, inverse);
        
        allOddIndices[1] = uniteTransformArrays(oddIndices1, oddIndices17, inverse);
        
        allOddIndices[2] = uniteTransformArrays(oddIndices2, oddIndices18, inverse);
        
        allOddIndices[3] = uniteTransformArrays(oddIndices3, oddIndices19, inverse);
        
        allOddIndices[4] = uniteTransformArrays(oddIndices4, oddIndices20, inverse);
        
        allOddIndices[5] = uniteTransformArrays(oddIndices5, oddIndices21, inverse);
        
        allOddIndices[6] = uniteTransformArrays(oddIndices6, oddIndices22, inverse);
        
        allOddIndices[7] = uniteTransformArrays(oddIndices7, oddIndices23, inverse);
        
        allOddIndices[8] = uniteTransformArrays(oddIndices8, oddIndices24, inverse);
        
        allOddIndices[9] = uniteTransformArrays(oddIndices9, oddIndices25, inverse);
        
        allOddIndices[10] = uniteTransformArrays(oddIndices10, oddIndices26, inverse);
        
        allOddIndices[11] = uniteTransformArrays(oddIndices11, oddIndices27, inverse);
        
        allOddIndices[12] = uniteTransformArrays(oddIndices12, oddIndices28, inverse);
        
        allOddIndices[13] = uniteTransformArrays(oddIndices13, oddIndices29, inverse);
        
        allOddIndices[14] = uniteTransformArrays(oddIndices14, oddIndices30, inverse);
        
        allOddIndices[15] = uniteTransformArrays(oddIndices15, oddIndices31, inverse);
        
        while (allOddIndices.length != 1) {
            Complex[][] temp = new Complex[(int) Math.floor(allOddIndices.length/2)][];
            for (int k = 0; k < temp.length; k++){
                temp[k] = uniteTransformArrays(allOddIndices[k], allOddIndices[k + (int) Math.floor(allOddIndices.length / 2)], inverse);
            }

            allOddIndices = temp;
        }

        Complex[] transformedArray = uniteTransformArrays(evenIndices, allOddIndices[0], inverse);

        for (int c = 0; c < n; c++) {
            array[c] = transformedArray[c];
        }

        // arrayInProgress.addAll(progress);
    }

    private static void primaryTransformWorker(Complex[] paddedArray, Complex[] oddIndices0, Complex[] oddIndices1, Complex[] oddIndices2, Complex[] oddIndices3, Complex[] oddIndices4, Complex[] oddIndices5, Complex[] oddIndices6, Complex[] oddIndices7, Complex[] oddIndices8, Complex[] oddIndices9, Complex[] oddIndices10, Complex[] oddIndices11, Complex[] oddIndices12, Complex[] oddIndices13, Complex[] oddIndices14, Complex[] oddIndices15, Complex[] oddIndices16, Complex[] oddIndices17, Complex[] oddIndices18, Complex[] oddIndices19, Complex[] oddIndices20, Complex[] oddIndices21, Complex[] oddIndices22, Complex[] oddIndices23, Complex[] oddIndices24, Complex[] oddIndices25, Complex[] oddIndices26, Complex[] oddIndices27, Complex[] oddIndices28, Complex[] oddIndices29, Complex[] oddIndices30, Complex[] oddIndices31, int c) {
        oddIndices0[c] = paddedArray[64* c + 1 + 0];

        oddIndices1[c] = paddedArray[64* c + 1 + 2];

        oddIndices2[c] = paddedArray[64* c + 1 + 4];

        oddIndices3[c] = paddedArray[64* c + 1 + 6];

        oddIndices4[c] = paddedArray[64* c + 1 + 8];

        oddIndices5[c] = paddedArray[64* c + 1 + 10];

        oddIndices6[c] = paddedArray[64* c + 1 + 12];

        oddIndices7[c] = paddedArray[64* c + 1 + 14];

        oddIndices8[c] = paddedArray[64* c + 1 + 16];

        oddIndices9[c] = paddedArray[64* c + 1 + 18];

        oddIndices10[c] = paddedArray[64* c + 1 + 20];

        oddIndices11[c] = paddedArray[64* c + 1 + 22];

        oddIndices12[c] = paddedArray[64* c + 1 + 24];

        oddIndices13[c] = paddedArray[64* c + 1 + 26];

        oddIndices14[c] = paddedArray[64* c + 1 + 28];

        oddIndices15[c] = paddedArray[64* c + 1 + 30];

        oddIndices16[c] = paddedArray[64* c + 1 + 32];

        oddIndices17[c] = paddedArray[64* c + 1 + 34];

        oddIndices18[c] = paddedArray[64* c + 1 + 36];

        oddIndices19[c] = paddedArray[64* c + 1 + 38];

        oddIndices20[c] = paddedArray[64* c + 1 + 40];

        oddIndices21[c] = paddedArray[64* c + 1 + 42];

        oddIndices22[c] = paddedArray[64* c + 1 + 44];

        oddIndices23[c] = paddedArray[64* c + 1 + 46];

        oddIndices24[c] = paddedArray[64* c + 1 + 48];

        oddIndices25[c] = paddedArray[64* c + 1 + 50];

        oddIndices26[c] = paddedArray[64* c + 1 + 52];

        oddIndices27[c] = paddedArray[64* c + 1 + 54];

        oddIndices28[c] = paddedArray[64* c + 1 + 56];

        oddIndices29[c] = paddedArray[64* c + 1 + 58];

        oddIndices30[c] = paddedArray[64* c + 1 + 60];

        oddIndices31[c] = paddedArray[64* c + 1 + 62];
    }

    // computes how much padding to add
    private static int assistant(Complex[] array, int n, boolean inverse) {
        int  numOff = n % (64);

        if ( numOff == 0 && ( !complex || inverse ) ) { 
            return 0;
        } else {
            return (64) - numOff; 
        }

    }

    private static void arrayIntake(Complex[] array){
        double count = 0;
        int total = 0;
        for (int p = 0; p < array.length; p++) {
            count++;
            total += array[p].getReal();
        }
        double meanVal = total/count;
        if (meanVal >= (BASE - 1)/2.0){
            complex = true;
        } else {
            complex = false;
        }
    }

    /**
     * This fft method takes in data in a float array and then transforms it using Complex arrays
     * because they are more accurate. When finished, it sets the data to be the real part of the
     * transformed Complex arrays. It loses the complex part of the transformed data.
     *
     * @param array to be transformed
     * @param n length of the data to be transformed
     * @param inverse is true if we want the inverse fft and false otherwise
     */
    public static void transform(float[] array, int n, boolean inverse) {
        Complex[] complexArray = new Complex[n];
        for (int a = 0; a < n; a++) {
            complexArray[a] = new Complex(array[a]);
        }
        primaryTransform(complexArray, n , inverse, new ArrayList<Complex>());
        for (int q = 0; q < n; q++) {
            if (inverse) {
                array[q] = (float) complexArray[q].divide(n).getReal();
            } else {
                array[q] = (float) complexArray[q].getReal();
            }
        }
        // arrayInProgress.clear();
    }

    /**
     * This fft method takes in data in a complex array and transforms that array.
     * This method does not lose any data.
     *
     * @param array to be transformed
     * @param n length of the data to be transformed
     * @param inverse is true if we want the inverse fft and false otherwise

     */
    public static void transform(Complex[] array, int n, boolean inverse) {
        primaryTransform(array, n , inverse, new ArrayList<Complex>());
        for (int i = 0; i < n; i++) {
            if (inverse) {
                array[i] = array[i].divide(n);
            }
        }
        // arrayInProgress.clear();
    }

    /**
     * @param inverse
     * @return
     */
    private static Complex[] uniteTransformArrays(Complex[] evenIndices, Complex[] oddIndices, boolean inverse) {

        Complex[] transformedArray = new Complex[evenIndices.length + oddIndices.length];
        int transformedSize = transformedArray.length;
        Complex omegaZero = new Complex(1);
        Complex omegaToMultiply = grabOmega(transformedSize,inverse);
        for (int c = 0; c < Math.floor(transformedSize /2); c++) {
            transformedArray[c] = omegaZero.multiply(oddIndices[c]).add(evenIndices[c]);
            int index = (int) (c + Math.floor(transformedSize /2));
            if (inverse) {
                transformedArray[index] = omegaZero.multiply(oddIndices[c]).negate().add(evenIndices[c]);
            } else {
                transformedArray[index] = omegaZero.multiply(oddIndices[c]).negate().add(evenIndices[c]);
            }
            omegaZero = omegaZero.multiply(omegaToMultiply);

        }
        return transformedArray;
    }

    private static Complex grabOmega(int n, boolean inverse) {
        if (inverse) {
            return (new Complex(Math.E)).pow(Complex.I.multiply((2*Math.PI)/n));
        }
        return (new Complex(Math.E)).pow(Complex.I.multiply((2*Math.PI)/n).negate());
    }
}
