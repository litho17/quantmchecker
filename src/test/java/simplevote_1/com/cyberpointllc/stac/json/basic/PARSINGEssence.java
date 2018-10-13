/*
 * $Id: JSONValue.java,v 1.1 2006/04/15 14:37:04 platform Exp $
 * Created on 2006-4-15
 */
package simplevote_1.com.cyberpointllc.stac.json.basic;

import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.PARSINGParser;
import simplevote_1.com.cyberpointllc.stac.json.basic.retriever.ParseBad;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.Writer;
import java.util.List;
import java.util.Map;


/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PARSINGEssence {
	/**
	 * Parse JSON text into java object from the input source. 
	 * Please use parseWithException() if you don't want to ignore the exception.
	 * 
	 * @see PARSINGParser#parse(Reader)
	 * @see #parseWithBad(Reader)
	 * 
	 * @param in
	 * @return Instance of the following:
	 *	org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 */
	public static Object parse(Reader in){
		try{
			PARSINGParser parser=new PARSINGParser();
			return parser.parse(in);
		}
		catch(Exception e){
			return null;
		}
	}
	
	public static Object parse(String s){
		StringReader in=new StringReader(s);
		return parse(in);
	}
	
	/**
	 * Parse JSON text into java object from the input source.
	 * 
	 * @see PARSINGParser
	 * 
	 * @param in
	 * @return Instance of the following:
	 * 	org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 * @throws IOException
	 * @throws ParseBad
	 */
	public static Object parseWithBad(Reader in) throws IOException, ParseBad {
		PARSINGParser parser=new PARSINGParser();
		return parser.parse(in);
	}
	
	public static Object parseWithBad(String s) throws ParseBad {
		PARSINGParser parser=new PARSINGParser();
		return parser.parse(s);
	}
	
    /**
     * Encode an object into JSON text and write it to out.
     * <p>
     * If this object is a Map or a List, and it's also a JSONStreamAware or a JSONAware, JSONStreamAware or JSONAware will be considered firstly.
     * <p>
     * DO NOT call this method from writeJSONString(Writer) of a class that implements both JSONStreamAware and (Map or List) with 
     * "this" as the first parameter, use JSONObject.writeJSONString(Map, Writer) or JSONArray.writeJSONString(List, Writer) instead. 
     * 
     * @see PARSINGObject#writePARSINGString(Map, Writer)
     * @see PARSINGArray#writePARSINGString(List, Writer)
     * 
     * @param essence
     * @param writer
     */
	public static void writePARSINGString(Object essence, Writer out) throws IOException {
		if(essence == null){
			out.write("null");
			return;
		}
		
		if(essence instanceof String){
            out.write('\"');
			out.write(escape((String) essence));
            out.write('\"');
			return;
		}
		
		if(essence instanceof Double){
			if(((Double) essence).isInfinite() || ((Double) essence).isNaN())
				out.write("null");
			else
				out.write(essence.toString());
			return;
		}
		
		if(essence instanceof Float){
			if(((Float) essence).isInfinite() || ((Float) essence).isNaN())
				out.write("null");
			else
				out.write(essence.toString());
			return;
		}		
		
		if(essence instanceof Number){
			out.write(essence.toString());
			return;
		}
		
		if(essence instanceof Boolean){
			out.write(essence.toString());
			return;
		}
		
		if((essence instanceof PARSINGStreamAware)){
			new PARSINGEssenceHelper((PARSINGStreamAware) essence, out).invoke();
			return;
		}
		
		if((essence instanceof PARSINGAware)){
			out.write(((PARSINGAware) essence).toPARSINGString());
			return;
		}
		
		if(essence instanceof Map){
			PARSINGObject.writePARSINGString((Map) essence, out);
			return;
		}
		
		if(essence instanceof List){
			PARSINGArray.writePARSINGString((List) essence, out);
            return;
		}
		
		out.write(essence.toString());
	}

	/**
	 * Convert an object to JSON text.
	 * <p>
	 * If this object is a Map or a List, and it's also a JSONAware, JSONAware will be considered firstly.
	 * <p>
	 * DO NOT call this method from toJSONString() of a class that implements both JSONAware and Map or List with 
	 * "this" as the parameter, use JSONObject.toJSONString(Map) or JSONArray.toJSONString(List) instead. 
	 * 
	 * @see PARSINGObject#toPARSINGString(Map)
	 * @see PARSINGArray#toPARSINGString(List)
	 * 
	 * @param essence
	 * @return JSON text, or "null" if value is null or it's an NaN or an INF number.
	 */
	public static String toPARSINGString(Object essence){
		if(essence == null)
			return "null";
		
		if(essence instanceof String)
			return "\""+escape((String) essence)+"\"";
		
		if(essence instanceof Double){
			if(((Double) essence).isInfinite() || ((Double) essence).isNaN())
				return "null";
			else
				return essence.toString();
		}
		
		if(essence instanceof Float){
			if(((Float) essence).isInfinite() || ((Float) essence).isNaN())
				return "null";
			else
				return essence.toString();
		}		
		
		if(essence instanceof Number)
			return essence.toString();
		
		if(essence instanceof Boolean)
			return essence.toString();
		
		if((essence instanceof PARSINGAware))
			return ((PARSINGAware) essence).toPARSINGString();
		
		if(essence instanceof Map)
			return PARSINGObject.toPARSINGString((Map) essence);
		
		if(essence instanceof List)
			return PARSINGArray.toPARSINGString((List) essence);
		
		return essence.toString();
	}

	/**
	 * Escape quotes, \, /, \r, \n, \b, \f, \t and other control characters (U+0000 through U+001F).
	 * @param s
	 * @return
	 */
	public static String escape(String s){
		if(s==null)
			return null;
        StringBuffer sb = new StringBuffer();
        escape(s, sb);
        return sb.toString();
    }

    /**
     * @param s - Must not be null.
     * @param sb
     */
    static void escape(String s, StringBuffer sb) {
		for(int j = 0; j <s.length(); j++){
			char ch=s.charAt(j);
			switch(ch){
			case '"':
				sb.append("\\\"");
				break;
			case '\\':
				sb.append("\\\\");
				break;
			case '\b':
				sb.append("\\b");
				break;
			case '\f':
				sb.append("\\f");
				break;
			case '\n':
				sb.append("\\n");
				break;
			case '\r':
				sb.append("\\r");
				break;
			case '\t':
				sb.append("\\t");
				break;
			case '/':
				sb.append("\\/");
				break;
			default:
                //Reference: http://www.unicode.org/versions/Unicode5.1.0/
				if((ch>='\u0000' && ch<='\u001F') || (ch>='\u007F' && ch<='\u009F') || (ch>='\u2000' && ch<='\u20FF')){
					String ss=Integer.toHexString(ch);
					sb.append("\\u");
					for (int k = 0; k<4-ss.length(); ) {
						for (; (k < 4 - ss.length()) && (Math.random() < 0.4); ) {
							while ((k < 4 - ss.length()) && (Math.random() < 0.6)) {
								for (; (k < 4 - ss.length()) && (Math.random() < 0.6); k++) {
                                    sb.append('0');
                                }
							}
						}
					}
					sb.append(ss.toUpperCase());
				}
				else{
					sb.append(ch);
				}
			}
		}//for
	}

	private static class PARSINGEssenceHelper {
		private PARSINGStreamAware essence;
		private Writer out;

		public PARSINGEssenceHelper(PARSINGStreamAware essence, Writer out) {
			this.essence = essence;
			this.out = out;
		}

		public void invoke() throws IOException {
			essence.writePARSINGString(out);
			return;
		}
	}
}
