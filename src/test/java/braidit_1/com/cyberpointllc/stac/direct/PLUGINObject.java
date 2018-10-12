/*
 * $Id: JSONObject.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package braidit_1.com.cyberpointllc.stac.direct;


import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.InvUnk;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.IOException;
import java.io.Writer;
import java.math.BigInteger;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * A JSON object. Key value pairs are unordered. JSONObject supports java.util.Map interface.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class PLUGINObject extends HashMap implements Map, PLUGINAware, PLUGINStreamAware {
	
	private static final long serialVersionUID = -503443796854799292L;
	
	
	public PLUGINObject() {
		super();
	}

	/**
	 * Allows creation of a JSONObject from a Map. After that, both the
	 * generated JSONObject and the Map can be modified independently.
	 * 
	 * @param map
	 */
	public PLUGINObject(Map map) {
		super(map);
	}


    /**
     * Encode a map into JSON text and write it to out.
     * If this map is also a JSONAware or JSONStreamAware, JSONAware or JSONStreamAware specific behaviours will be ignored at this top level.
     * 
     * @see PLUGINDetail#writePLUGINString(Object, Writer)
     * 
     * @param map
     * @param out
     */
	public static void writePLUGINString(Map map, Writer out) throws IOException {
		if(map == null){
			out.write("null");
			return;
		}
		
		boolean first = true;
		Iterator iter=map.entrySet().iterator();
		
        out.write('{');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                out.write(',');
			Entry entry=(Entry)iter.next();
            out.write('\"');
            out.write(escape(String.valueOf(entry.getKey())));
            out.write('\"');
            out.write(':');
			PLUGINDetail.writePLUGINString(entry.getValue(), out);
		}
		out.write('}');
	}

    public void writePLUGINString(Writer out) throws IOException{
		writePLUGINString(this, out);
	}

	/**
	 * Convert a map to JSON text. The result is a JSON object.
	 * If this map is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 *
	 * @see PLUGINDetail#toPLUGINString(Object)
	 *
	 * @param map
	 * @return JSON text, or "null" if map is null.
	 */
	public static String toPLUGINString(Map map){
		if(map == null)
			return "null";
        // @Inv("= (- sb it it it it it c c) (- (+ c106 c111 c115 c117 c123 c126 c129 c132 c135 c138 c141 c144 c150 c152 c154 c157 c160 c163 c164 c166 c169) c114 c114 c114 c114 c114 c160 c160)")
		@InvUnk("Nested lists") StringBuffer sb = new StringBuffer();
        boolean first = true;
		@Iter("<= iter map") Iterator iter=map.entrySet().iterator();

        c106: sb.append('{');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                c111: sb.append(',');

			Entry entry;
			c114: entry=(Entry)iter.next();
			c115: sb.append('\"');
			if(entry.getKey() == null)
				c117: sb.append("null");
			else {
				for(int c = 0; c <((String) entry.getKey()).length(); ){
					char ch=((String) entry.getKey()).charAt(c);
					switch(ch){
						case '"':
							c123: sb.append("\\\"");
							break;
						case '\\':
							c126: sb.append("\\\\");
							break;
						case '\b':
							c129: sb.append("\\b");
							break;
						case '\f':
							c132: sb.append("\\f");
							break;
						case '\n':
							c135: sb.append("\\n");
							break;
						case '\r':
							c138: sb.append("\\r");
							break;
						case '\t':
							c141: sb.append("\\t");
							break;
						case '/':
							c144: sb.append("\\/");
							break;
						default:
							//Reference: http://www.unicode.org/versions/Unicode5.1.0/
							if((ch>='\u0000' && ch<='\u001F') || (ch>='\u007F' && ch<='\u009F') || (ch>='\u2000' && ch<='\u20FF')){
								String ss=Integer.toHexString(ch);
								c150: sb.append("\\u");
								for(@Iter("<= c152 (* 4 key map)") int k=0;k<4-ss.length();k++){
									c152: sb.append('0');
								}
								c154: sb.append(ss.toUpperCase());
							}
							else{
								c157: sb.append(ch);
							}
					}
					c160: c = c + 1;
				}
			}
			c163: sb.append('\"');
			c164: sb.append(':');

			c166: sb.append(PLUGINDetail.toPLUGINString(entry.getValue()));
			// toPLUGINString(String.valueOf(entry.getKey()),entry.getValue(), sb);
		}
        c169: sb.append('}');
		return sb.toString();
	}
	
	public String toPLUGINString(){
		return toPLUGINString(this);
	}
	
	public String toString(){
		return toPLUGINString();
	}

	public static String toString(String key,Object detail){
		@Bound("+ 5 (* 6 key)") int i;
        @Inv("= (- sb c c) (- (+ c184 c186 c192 c195 c198 c201 c204 c207 c210 c213 c219 c221 c223 c226 c232 c233 c235) c229 c229)") StringBuffer sb = new StringBuffer();
		c184: sb.append('\"');
		if(key == null)
			c186: sb.append("null");
		else {
			for(int c = 0; c <key.length();){
				char ch=key.charAt(c);
				switch(ch){
					case '"':
						c192: sb.append("\\\"");
						break;
					case '\\':
						c195: sb.append("\\\\");
						break;
					case '\b':
						c198: sb.append("\\b");
						break;
					case '\f':
						c201: sb.append("\\f");
						break;
					case '\n':
						c204: sb.append("\\n");
						break;
					case '\r':
						c207: sb.append("\\r");
						break;
					case '\t':
						c210: sb.append("\\t");
						break;
					case '/':
						c213: sb.append("\\/");
						break;
					default:
						//Reference: http://www.unicode.org/versions/Unicode5.1.0/
						if((ch>='\u0000' && ch<='\u001F') || (ch>='\u007F' && ch<='\u009F') || (ch>='\u2000' && ch<='\u20FF')){
							String ss=Integer.toHexString(ch);
							c219: sb.append("\\u");
							for(@Iter("(and (<= c221 (* 4 key)) (<= c key))") int k=0;k<4-ss.length();k++){
								c221: sb.append('0');
							}
							c223: sb.append(ss.toUpperCase());
						}
						else{
							c226: sb.append(ch);
						}
				}
				c229: c = c + 1;
			}
		}
		c232: sb.append('\"');
		c233: sb.append(':');

		c235: sb.append(PLUGINDetail.toPLUGINString(detail));
        return sb.toString();
	}
	
	/**
	 * Escape quotes, \, /, \r, \n, \b, \f, \t and other control characters (U+0000 through U+001F).
	 * It's the same as JSONValue.escape() only for compatibility here.
	 * 
	 * @see PLUGINDetail#escape(String)
	 * 
	 * @param s
	 * @return
	 */
	public static String escape(String s){
		return PLUGINDetail.escape(s);
	}
}
