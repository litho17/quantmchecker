package braidit_1.com.cyberpointllc.stac.jack.direct.grabber;

import java.util.List;
import java.util.Map;

/**
 * Container factory for creating containers for JSON object and JSON array.
 * 
 * @see OBJNOTEParser#parse(java.io.Reader, ContainerFactory)
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface ContainerFactory {
	/**
	 * @return A Map instance to store JSON object, or null if you want to use org.json.simple.JSONObject.
	 */
	Map composeObjectContainer();
	
	/**
	 * @return A List instance to store JSON array, or null if you want to use org.json.simple.JSONArray. 
	 */
	List creatArrayContainer();
}
