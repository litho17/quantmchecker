package powerbroker_1.edu.networkcusp.direct;

import java.io.IOException;
import java.io.Writer;

/**
 * Beans that support customized output of JSON text to a writer shall implement this interface.  
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface PLUGINStreamAware {
	/**
	 * write JSON string to out.
	 */
	void writePLUGINString(Writer out) throws IOException;
}
