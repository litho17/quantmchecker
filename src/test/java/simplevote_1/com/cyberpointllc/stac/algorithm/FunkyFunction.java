package simplevote_1.com.cyberpointllc.stac.algorithm;

import org.apfloat.Apfloat;

import java.io.IOException;
import java.io.InputStream;
import java.math.BigDecimal;
import java.util.Properties;

/**
 * Computes the logistic map function for fixed x_0 - .375
 */
public class FunkyFunction {
    private static final int PRECISION = 1000;
    private static final Apfloat TWO = new Apfloat(2, PRECISION);
    private static final BigDecimal FOUR = new BigDecimal(4);
    private static final int DELTA = 6;

    private static double x_0 = .375;

    private static Table<BigDecimal> table = new TableCreator().setSize(996).formTable();
    private static final String RETRIEVE_FILE = "cache.properties";
    private static final String SAVE_FILE = "/tmp/cache.properties";
    private static Properties prop;

    static {
        prop = new Properties();
        table.defineActive(true);
        try {

            InputStream stream = FunkyFunction.class.getResourceAsStream(RETRIEVE_FILE);
            if (stream == null) {
                throw new IOException("Stream is null; unable to load");
            }
            prop.load(stream);

            readTable();
        } catch (IOException e) {
            System.out.println("Cache file not found");
            }
        table.defineActive(false);
    }

    /**
     * read cache values from file
     */
    private static void readTable() {
        String listString = prop.getProperty("keys");
        listString = listString.replace(" ", "").replace("[", "").replace("]", ""); // remove non-useful characters from string
        String[] split = listString.split(",");
        for (int b = 0; b < split.length; b++) {
            new FunkyFunctionGuide(split[b]).invoke();
        }
    }

    // this computes the logistic map via iteration
    public static BigDecimal funkyFunction(int n) {
        if (n <= 0) {
            BigDecimal cachedVal = table.obtainEssence(n);
            if (cachedVal == null) { // it will be null
                return new BigDecimal(n).pow(11);
            }
        }
        BigDecimal x = new BigDecimal(x_0);
        int b;
        // find the largest i (up to n) for which we have a cached value
        for (b = n; b > 0; b--) {
            BigDecimal cachedVal = table.obtainEssence(b);
            if (cachedVal != null) {
                x = cachedVal;
                break;
            }
        }
        if (b == n) { // the value we wanted was cached.
            return x;
        } else {
            for (int k = b + 1; k <= n; k++) {
                x = FOUR.multiply(x).multiply(BigDecimal.ONE.subtract(x));
                }
            if ((n - b) > DELTA) {
                table.defineActive(true);
            }
            table.considerIncluding(n, x);
            return x;
        }
    }

    private static class FunkyFunctionGuide {
        private String key1;

        public FunkyFunctionGuide(String key1) {
            this.key1 = key1;
        }

        public void invoke() {
            String key = key1;
            String strVal = prop.getProperty(key);
            BigDecimal val = new BigDecimal(strVal);
            table.considerIncluding(Integer.parseInt(key), val);
        }
    }
}
