package braidit_1.com.cyberpointllc.stac.jack.direct;

/**
 * Beans that support customized output of JSON text shall implement this interface.  
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface OBJNOTEAware {
	/**
	 * @return JSON text
	 */
	String toOBJNOTEString();
}
