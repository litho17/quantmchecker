/*
 * $Id: JSONValue.java,v 1.1 2006/04/15 14:37:04 platform Exp $
 * Created on 2006-4-15
 */
package braidit_1.com.cyberpointllc.stac.jack.direct;

import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.OBJNOTEParser;
import braidit_1.com.cyberpointllc.stac.jack.direct.grabber.ParseException;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.Writer;
import java.util.List;
import java.util.Map;


/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class OBJNOTECore {
	/**
	 * Parse JSON text into java object from the input source. 
	 * Please use parseWithException() if you don't want to ignore the exception.
	 * 
	 * @see OBJNOTEParser#parse(Reader)
	 * @see #parseWithException(Reader)
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
			OBJNOTEParser parser=new OBJNOTEParser();
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
	 * @see OBJNOTEParser
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
	 * @throws ParseException
	 */
	public static Object parseWithException(Reader in) throws IOException, ParseException{
		OBJNOTEParser parser=new OBJNOTEParser();
		return parser.parse(in);
	}
	
	public static Object parseWithException(String s) throws ParseException{
		OBJNOTEParser parser=new OBJNOTEParser();
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
     * @see OBJNOTEObject#writeOBJNOTEString(Map, Writer)
     * @see OBJNOTEArray#writeOBJNOTEString(List, Writer)
     * 
     * @param core
     * @param writer
     */
	public static void writeOBJNOTEString(Object core, Writer out) throws IOException {
		if(core == null){
			out.write("null");
			return;
		}
		
		if(core instanceof String){
            out.write('\"');
			out.write(escape((String) core));
            out.write('\"');
			return;
		}
		
		if(core instanceof Double){
			if(((Double) core).isInfinite() || ((Double) core).isNaN())
				out.write("null");
			else
				out.write(core.toString());
			return;
		}
		
		if(core instanceof Float){
			if(((Float) core).isInfinite() || ((Float) core).isNaN())
				out.write("null");
			else
				out.write(core.toString());
			return;
		}		
		
		if(core instanceof Number){
			out.write(core.toString());
			return;
		}
		
		if(core instanceof Boolean){
			out.write(core.toString());
			return;
		}
		
		if((core instanceof OBJNOTEStreamAware)){
			((OBJNOTEStreamAware) core).writeOBJNOTEString(out);
			return;
		}
		
		if((core instanceof OBJNOTEAware)){
			out.write(((OBJNOTEAware) core).toOBJNOTEString());
			return;
		}
		
		if(core instanceof Map){
			OBJNOTEObject.writeOBJNOTEString((Map) core, out);
			return;
		}
		
		if(core instanceof List){
			OBJNOTEArray.writeOBJNOTEString((List) core, out);
            return;
		}
		
		out.write(core.toString());
	}

	/**
	 * Convert an object to JSON text.
	 * <p>
	 * If this object is a Map or a List, and it's also a JSONAware, JSONAware will be considered firstly.
	 * <p>
	 * DO NOT call this method from toJSONString() of a class that implements both JSONAware and Map or List with 
	 * "this" as the parameter, use JSONObject.toJSONString(Map) or JSONArray.toJSONString(List) instead. 
	 * 
	 * @see OBJNOTEObject#toOBJNOTEString(Map)
	 * @see OBJNOTEArray#toOBJNOTEString(List)
	 * 
	 * @param core
	 * @return JSON text, or "null" if value is null or it's an NaN or an INF number.
	 */
	public static String toOBJNOTEString(Object core){
		if(core == null)
			return "null";
		
		if(core instanceof String)
			return "\""+escape((String) core)+"\"";
		
		if(core instanceof Double){
			if(((Double) core).isInfinite() || ((Double) core).isNaN())
				return "null";
			else
				return core.toString();
		}
		
		if(core instanceof Float){
			if(((Float) core).isInfinite() || ((Float) core).isNaN())
				return "null";
			else
				return core.toString();
		}		
		
		if(core instanceof Number)
			return core.toString();
		
		if(core instanceof Boolean)
			return core.toString();
		
		if((core instanceof OBJNOTEAware))
			return ((OBJNOTEAware) core).toOBJNOTEString();
		
		if(core instanceof Map)
			return OBJNOTEObject.toOBJNOTEString((Map) core);
		
		if(core instanceof List)
			return OBJNOTEArray.toOBJNOTEString((List) core);
		
		return core.toString();
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
		for(int i=0;i<s.length();i++){
			char ch=s.charAt(i);
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
					for(int k=0;k<4-ss.length();k++){
						sb.append('0');
					}
					sb.append(ss.toUpperCase());
				}
				else{
					sb.append(ch);
				}
			}
		}//for
	}

}
