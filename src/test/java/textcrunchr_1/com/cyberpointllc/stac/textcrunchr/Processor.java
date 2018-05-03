package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import java.io.InputStream;
import java.io.IOException;
import textcrunchr_1.com.cyberpointllc.stac.textcrunchr.TCResult;
import java.util.Map;

public abstract class Processor {

    public abstract TCResult process(InputStream inps) throws IOException;

    public abstract String getName();
}
