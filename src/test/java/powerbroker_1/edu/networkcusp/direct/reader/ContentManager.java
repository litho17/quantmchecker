package powerbroker_1.edu.networkcusp.direct.reader;

import java.io.IOException;

/**
 * A simplified and stoppable SAX-like content handler for stream processing of JSON text. 
 * 
 * @see org.xml.sax.ContentHandler
 * @see PLUGINGrabber#parse(java.io.Reader, ContentManager, boolean)
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public interface ContentManager {
	/**
	 * Receive notification of the beginning of JSON processing.
	 * The parser will invoke this method only once.
     * 
	 * @throws ParseDeviation
	 * 			- JSONParser will stop and throw the same exception to the caller when receiving this exception.
	 */
	void startPLUGIN() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the end of JSON processing.
	 * 
	 * @throws ParseDeviation
	 */
	void endPLUGIN() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON object.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     *          - JSONParser will stop and throw the same exception to the caller when receiving this exception.
     * @see #endPLUGIN
	 */
	boolean startObject() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the end of a JSON object.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     * 
     * @see #startObject
	 */
	boolean endObject() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON object entry.
	 * 
	 * @param key - Key of a JSON object entry. 
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     * 
     * @see #endObjectEntry
	 */
	boolean startObjectEntry(String key) throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the end of the value of previous object entry.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     * 
     * @see #startObjectEntry
	 */
	boolean endObjectEntry() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the beginning of a JSON array.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     * 
     * @see #endArray
	 */
	boolean startArray() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the end of a JSON array.
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
     * 
     * @see #startArray
	 */
	boolean endArray() throws ParseDeviation, IOException;
	
	/**
	 * Receive notification of the JSON primitive values:
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean
	 * 	null
	 * 
	 * @param detail - Instance of the following:
	 * 			java.lang.String,
	 * 			java.lang.Number,
	 * 			java.lang.Boolean
	 * 			null
	 * 
	 * @return false if the handler wants to stop parsing after return.
	 * @throws ParseDeviation
	 */
	boolean primitive(Object detail) throws ParseDeviation, IOException;
		
}
