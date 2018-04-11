/*
 * $Id: JSONValue.java,v 1.1 2006/04/15 14:37:04 platform Exp $
 * Created on 2006-4-15
 */
package battleboats_1.com.cyberpointllc.stac.objnote.direct;

import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.PLUGINGrabber;
import battleboats_1.com.cyberpointllc.stac.objnote.direct.reader.ParseDeviation;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.Writer;
import java.util.List;
import java.util.Map;


/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PLUGINDetail {
	/**
	 * Parse JSON text into java object from the input source. 
	 * Please use parseWithException() if you don't want to ignore the exception.
	 * 
	 * @see PLUGINGrabber#parse(Reader)
	 * @see #parseWithDeviation(Reader)
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
			PLUGINGrabber grabber =new PLUGINGrabber();
			return grabber.parse(in);
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
	 * @see PLUGINGrabber
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
	 * @throws ParseDeviation
	 */
	public static Object parseWithDeviation(Reader in) throws IOException, ParseDeviation {
		PLUGINGrabber grabber =new PLUGINGrabber();
		return grabber.parse(in);
	}
	
	public static Object parseWithDeviation(String s) throws ParseDeviation {
		PLUGINGrabber grabber =new PLUGINGrabber();
		return grabber.parse(s);
	}
	
    /**
     * Encode an object into JSON text and write it to out.
     * <p>
     * If this object is a Map or a List, and it's also a JSONStreamAware or a JSONAware, JSONStreamAware or JSONAware will be considered firstly.
     * <p>
     * DO NOT call this method from writeJSONString(Writer) of a class that implements both JSONStreamAware and (Map or List) with 
     * "this" as the first parameter, use JSONObject.writeJSONString(Map, Writer) or JSONArray.writeJSONString(List, Writer) instead. 
     * 
     * @see PLUGINObject#writePLUGINString(Map, Writer)
     * @see PLUGINArray#writePLUGINString(List, Writer)
     * 
     * @param detail
     * @param writer
     */
	public static void writePLUGINString(Object detail, Writer out) throws IOException {
		if(detail == null){
			out.write("null");
			return;
		}
		
		if(detail instanceof String){
            out.write('\"');
			out.write(escape((String) detail));
            out.write('\"');
			return;
		}
		
		if(detail instanceof Double){
			if(((Double) detail).isInfinite() || ((Double) detail).isNaN())
				out.write("null");
			else
				out.write(detail.toString());
			return;
		}
		
		if(detail instanceof Float){
			if(((Float) detail).isInfinite() || ((Float) detail).isNaN())
				out.write("null");
			else
				out.write(detail.toString());
			return;
		}		
		
		if(detail instanceof Number){
			out.write(detail.toString());
			return;
		}
		
		if(detail instanceof Boolean){
			out.write(detail.toString());
			return;
		}
		
		if((detail instanceof PLUGINStreamAware)){
			((PLUGINStreamAware) detail).writePLUGINString(out);
			return;
		}
		
		if((detail instanceof PLUGINAware)){
			out.write(((PLUGINAware) detail).toPLUGINString());
			return;
		}
		
		if(detail instanceof Map){
			PLUGINObject.writePLUGINString((Map) detail, out);
			return;
		}
		
		if(detail instanceof List){
			PLUGINArray.writePLUGINString((List) detail, out);
            return;
		}
		
		out.write(detail.toString());
	}

	/**
	 * Convert an object to JSON text.
	 * <p>
	 * If this object is a Map or a List, and it's also a JSONAware, JSONAware will be considered firstly.
	 * <p>
	 * DO NOT call this method from toJSONString() of a class that implements both JSONAware and Map or List with 
	 * "this" as the parameter, use JSONObject.toJSONString(Map) or JSONArray.toJSONString(List) instead. 
	 * 
	 * @see PLUGINObject#toPLUGINString(Map)
	 * @see PLUGINArray#toPLUGINString(List)
	 * 
	 * @param detail
	 * @return JSON text, or "null" if value is null or it's an NaN or an INF number.
	 */
	public static String toPLUGINString(Object detail){
		if(detail == null)
			return "null";
		
		if(detail instanceof String)
			return "\""+escape((String) detail)+"\"";
		
		if(detail instanceof Double){
			if(((Double) detail).isInfinite() || ((Double) detail).isNaN())
				return "null";
			else
				return detail.toString();
		}
		
		if(detail instanceof Float){
			if(((Float) detail).isInfinite() || ((Float) detail).isNaN())
				return "null";
			else
				return detail.toString();
		}		
		
		if(detail instanceof Number)
			return detail.toString();
		
		if(detail instanceof Boolean)
			return detail.toString();
		
		if((detail instanceof PLUGINAware))
			return ((PLUGINAware) detail).toPLUGINString();
		
		if(detail instanceof Map)
			return PLUGINObject.toPLUGINString((Map) detail);
		
		if(detail instanceof List)
			return PLUGINArray.toPLUGINString((List) detail);
		
		return detail.toString();
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
		for(int c = 0; c <s.length(); c++){
			char ch=s.charAt(c);
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
