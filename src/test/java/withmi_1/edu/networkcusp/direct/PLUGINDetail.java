/*
 * $Id: JSONValue.java,v 1.1 2006/04/15 14:37:04 platform Exp $
 * Created on 2006-4-15
 */
package withmi_1.edu.networkcusp.direct;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;
import withmi_1.edu.networkcusp.direct.reader.ContainerFactory;
import withmi_1.edu.networkcusp.direct.reader.PLUGINGrabber;

import java.io.IOException;
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
	 *
	 *
	 * @return Instance of the following:
	 *	org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 */
	
	public static Object parse(String s){
		StringReader in=new StringReader(s);
		try{
			@InvUnk("Complex loop") PLUGINGrabber grabber =new PLUGINGrabber();
			return grabber.parse(in, (ContainerFactory)null);
		}
		catch(Exception e){
			return null;
		}
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
		@Bound("* 6 s") int i;
        @Inv("= (- sb c c) (- (+ c198 c201 c204 c207 c210 c213 c216 c219 c225 c227 c229 c232) c235 c235)") StringBuffer sb = new StringBuffer();
		for(int c = 0; c <s.length(); ){
			char ch=s.charAt(c);
			switch(ch){
				case '"':
					c198: sb.append("\\\"");
					break;
				case '\\':
					c201: sb.append("\\\\");
					break;
				case '\b':
					c204: sb.append("\\b");
					break;
				case '\f':
					c207: sb.append("\\f");
					break;
				case '\n':
					c210: sb.append("\\n");
					break;
				case '\r':
					c213: sb.append("\\r");
					break;
				case '\t':
					c216: sb.append("\\t");
					break;
				case '/':
					c219: sb.append("\\/");
					break;
				default:
					//Reference: http://www.unicode.org/versions/Unicode5.1.0/
					if((ch>='\u0000' && ch<='\u001F') || (ch>='\u007F' && ch<='\u009F') || (ch>='\u2000' && ch<='\u20FF')){
						String ss=Integer.toHexString(ch);
						c225: sb.append("\\u");
						for(@Iter("(and (<= c227 (* 4 s)) (<= c s))") int k = 0; k<4-ss.length(); k++){
							c227: sb.append('0');
						}
						c229: sb.append(ss.toUpperCase());
					}
					else{
						c232: sb.append(ch);
					}
			}
			c235: c = c + 1;
		}
        return sb.toString();
    }

    /**
     * @param s - Must not be null.
     * @param sb
     */

}
