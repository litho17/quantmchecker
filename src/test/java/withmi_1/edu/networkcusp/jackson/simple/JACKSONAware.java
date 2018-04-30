package withmi_1.edu.networkcusp.jackson.simple;

/**
 * Beans that support customized output of JSON text shall implement this interface.  
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface JACKSONAware {
	/**
	 * @return JSON text
	 */
	String toJACKSONString();
}
