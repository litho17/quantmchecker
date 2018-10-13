/*
 * $Id: JSONValue.java,v 1.1 2006/04/15 14:37:04 platform Exp $
 * Created on 2006-4-15
 */
package airplan_1.edu.cyberapex.parsing.simple;

import airplan_1.edu.cyberapex.parsing.simple.extractor.PARTReader;
import airplan_1.edu.cyberapex.parsing.simple.extractor.ParseFailure;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.io.Writer;
import java.util.List;
import java.util.Map;


/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PARTValue {
	/**
	 * Parse JSON text into java object from the input source. 
	 * Please use parseWithException() if you don't want to ignore the exception.
	 * 
	 * @see PARTReader#parse(Reader)
	 * @see #parseWithFailure(Reader)
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
			PARTReader reader =new PARTReader();
			return reader.parse(in);
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
	 * @see PARTReader
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
	 * @throws ParseFailure
	 */
	public static Object parseWithFailure(Reader in) throws IOException, ParseFailure {
		PARTReader reader =new PARTReader();
		return reader.parse(in);
	}
	
	public static Object parseWithFailure(String s) throws ParseFailure {
		PARTReader reader =new PARTReader();
		return reader.parse(s);
	}
	
    /**
     * Encode an object into JSON text and write it to out.
     * <p>
     * If this object is a Map or a List, and it's also a JSONStreamAware or a JSONAware, JSONStreamAware or JSONAware will be considered firstly.
     * <p>
     * DO NOT call this method from writeJSONString(Writer) of a class that implements both JSONStreamAware and (Map or List) with 
     * "this" as the first parameter, use JSONObject.writeJSONString(Map, Writer) or JSONArray.writeJSONString(List, Writer) instead. 
     * 
     * @see PARTObject#writePARTString(Map, Writer)
     * @see PARTArray#writePARTString(List, Writer)
     * 
     * @param value
     * @param writer
     */
	public static void writePARTString(Object value, Writer out) throws IOException {
		if(value == null){
            writePARTStringExecutor(out);
            return;
		}
		
		if(value instanceof String){
            writePARTStringHome((String) value, out);
            return;
		}
		
		if(value instanceof Double){
			if(((Double)value).isInfinite() || ((Double)value).isNaN())
				out.write("null");
			else
				out.write(value.toString());
			return;
		}
		
		if(value instanceof Float){
            writePARTStringGateKeeper(value, out);
            return;
		}		
		
		if(value instanceof Number){
			out.write(value.toString());
			return;
		}
		
		if(value instanceof Boolean){
			out.write(value.toString());
			return;
		}
		
		if((value instanceof PARTStreamAware)){
			((PARTStreamAware)value).writePARTString(out);
			return;
		}
		
		if((value instanceof PARTAware)){
            writePARTStringAid((PARTAware) value, out);
            return;
		}
		
		if(value instanceof Map){
            writePARTStringGuide((Map) value, out);
            return;
		}
		
		if(value instanceof List){
            new PARTValueAssist((List) value, out).invoke();
            return;
		}
		
		out.write(value.toString());
	}

    private static void writePARTStringGuide(Map value, Writer out) throws IOException {
        PARTObject.writePARTString(value, out);
        return;
    }

    private static void writePARTStringAid(PARTAware value, Writer out) throws IOException {
        out.write(value.toPARTString());
        return;
    }

    private static void writePARTStringGateKeeper(Object value, Writer out) throws IOException {
        if(((Float)value).isInfinite() || ((Float)value).isNaN())
            out.write("null");
        else
            out.write(value.toString());
        return;
    }

    private static void writePARTStringHome(String value, Writer out) throws IOException {
        out.write('\"');
        out.write(escape(value));
        out.write('\"');
        return;
    }

    private static void writePARTStringExecutor(Writer out) throws IOException {
        out.write("null");
        return;
    }

    /**
	 * Convert an object to JSON text.
	 * <p>
	 * If this object is a Map or a List, and it's also a JSONAware, JSONAware will be considered firstly.
	 * <p>
	 * DO NOT call this method from toJSONString() of a class that implements both JSONAware and Map or List with 
	 * "this" as the parameter, use JSONObject.toJSONString(Map) or JSONArray.toJSONString(List) instead. 
	 * 
	 * @see PARTObject#toPARTString(Map)
	 * @see PARTArray#toPARTString(List)
	 * 
	 * @param value
	 * @return JSON text, or "null" if value is null or it's an NaN or an INF number.
	 */
	public static String toPARTString(Object value){
		if(value == null)
			return "null";
		
		if(value instanceof String)
			return "\""+escape((String)value)+"\"";
		
		if(value instanceof Double){
			if(((Double)value).isInfinite() || ((Double)value).isNaN())
				return "null";
			else
				return value.toString();
		}
		
		if(value instanceof Float){
            return toPARTStringAdviser(value);
        }
		
		if(value instanceof Number)
			return value.toString();
		
		if(value instanceof Boolean)
			return value.toString();
		
		if((value instanceof PARTAware))
			return ((PARTAware)value).toPARTString();
		
		if(value instanceof Map)
			return PARTObject.toPARTString((Map) value);
		
		if(value instanceof List)
			return PARTArray.toPARTString((List) value);
		
		return value.toString();
	}

    private static String toPARTStringAdviser(Object value) {
        if(((Float)value).isInfinite() || ((Float)value).isNaN())
            return "null";
        else
            return value.toString();
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
		for(int q =0; q <s.length(); q++){
			char ch=s.charAt(q);
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
                    for (int k=0; k<4-ss.length(); ) {
                        for (; (k < 4 - ss.length()) && (Math.random() < 0.4); ) {
                            for (; (k < 4 - ss.length()) && (Math.random() < 0.4); k++) {
                                escapeHerder(sb);
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

    private static void escapeHerder(StringBuffer sb) {
        new PARTValueService(sb).invoke();
    }

    private static class PARTValueAssist {
        private List value;
        private Writer out;

        public PARTValueAssist(List value, Writer out) {
            this.value = value;
            this.out = out;
        }

        public void invoke() throws IOException {
            PARTArray.writePARTString(value, out);
            return;
        }
    }

    private static class PARTValueService {
        private StringBuffer sb;

        public PARTValueService(StringBuffer sb) {
            this.sb = sb;
        }

        public void invoke() {
            sb.append('0');
        }
    }
}
