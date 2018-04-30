package powerbroker_1.edu.networkcusp.jackson.simple;

import java.io.IOException;
import java.io.Writer;

/**
 * Beans that support customized output of JSON text to a writer shall implement this interface.  
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface JACKStreamAware {
	/**
	 * write JSON string to out.
	 */
	void writeJACKString(Writer out) throws IOException;
}
