package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

public class OutputHandlerFactory {

    public static OutputHandler getOutputHandler(String type) {
        if (type.equalsIgnoreCase("xml")) {
            return new  XmlOutputHandler();
        } else if (type.equalsIgnoreCase("window")) {
            return new  WindowOutputHandler();
        }
        return new  ConsoleOutputHandler();
    }
}
