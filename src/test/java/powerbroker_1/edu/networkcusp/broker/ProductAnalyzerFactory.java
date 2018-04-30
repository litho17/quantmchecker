package powerbroker_1.edu.networkcusp.broker;

public class ProductAnalyzerFactory {
    public static ProductAnalyzer form() {
        return new SimpleProductAnalyzer();
    }
}
