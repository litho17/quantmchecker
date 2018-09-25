package textcrunchr_1.com.cyberpointllc.stac.textcrunchr;

import java.io.IOException;
import java.io.InputStream;

public abstract class Processor {

    public abstract TCResult process(InputStream inps) throws IOException;

    public abstract String getName();
}
