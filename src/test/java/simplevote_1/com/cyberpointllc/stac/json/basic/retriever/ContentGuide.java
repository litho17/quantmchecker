package simplevote_1.com.cyberpointllc.stac.json.basic.retriever;

import java.io.IOException;

/**
 * A simplified and stoppable SAX-like content handler for stream processing of JSON text. 
 * 
 * @see org.xml.sax.ContentHandler
 * @see PARSINGParser#parse(java.io.Reader, ContentGuide, boolean)
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface ContentGuide {
	/**
	 * Receive notification of the beginning of JSON processing.
	 * The parser will invoke this method only once.
     * 
	 * @throws ParseBad
	 * 			- JSONParser will stop and throw the same exception to the caller when receiving this exception.
	 */
	void startPARSING() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the end of JSON processing.
	 * 
	 * @throws ParseBad
	 */
	void endPARSING() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON object.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     *          - JSONParser will stop and throw the same exception to the caller when receiving this exception.
     * @see #endPARSING
	 */
	boolean startObject() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the end of a JSON object.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     * 
     * @see #startObject
	 */
	boolean endObject() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON object entry.
	 * 
	 * @param key - Key of a JSON object entry. 
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     * 
     * @see #endObjectEntry
	 */
	boolean startObjectEntry(String key) throws ParseBad, IOException;
	
	/**
	 * Receive notification of the end of the value of previous object entry.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     * 
     * @see #startObjectEntry
	 */
	boolean endObjectEntry() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON array.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     * 
     * @see #endArray
	 */
	boolean startArray() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the end of a JSON array.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
     * 
     * @see #startArray
	 */
	boolean endArray() throws ParseBad, IOException;
	
	/**
	 * Receive notification of the JSON primitive values:
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean
	 * 	null
	 * 
	 * @param essence - Instance of the following:
	 * 			java.lang.String,
	 * 			java.lang.Number,
	 * 			java.lang.Boolean
	 * 			null
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseBad
	 */
	boolean primitive(Object essence) throws ParseBad, IOException;
		
}
