package simplevote_1.com.cyberpointllc.stac.json.basic;

/**
 * Beans that support customized output of JSON text shall implement this interface.  
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface PARSINGAware {
	/**
	 * @return JSON text
	 */
	String toPARSINGString();
}
