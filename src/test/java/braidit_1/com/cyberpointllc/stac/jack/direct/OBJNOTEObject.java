/*
 * $Id: JSONObject.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-10
 */
package braidit_1.com.cyberpointllc.stac.jack.direct;


import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Input;
import plv.colorado.edu.quantmchecker.qual.Inv;
import plv.colorado.edu.quantmchecker.qual.Iter;

import java.io.IOException;
import java.io.Writer;
import java.util.HashMap;
import java.util.Iterator;
import java.util.Map;

/**
 * A JSON object. Key value pairs are unordered. JSONObject supports java.util.Map interface.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class OBJNOTEObject extends HashMap implements Map, OBJNOTEAware, OBJNOTEStreamAware {
	
	private static final long serialVersionUID = -503443796854799292L;
	
	
	public OBJNOTEObject() {
		super();
	}

	/**
	 * Allows creation of a JSONObject from a Map. After that, both the
	 * generated JSONObject and the Map can be modified independently.
	 * 
	 * @param map
	 */
	public OBJNOTEObject(Map map) {
		super(map);
	}


    /**
     * Encode a map into JSON text and write it to out.
     * If this map is also a JSONAware or JSONStreamAware, JSONAware or JSONStreamAware specific behaviours will be ignored at this top level.
     * 
     * @see OBJNOTECore#writeOBJNOTEString(Object, Writer)
     * 
     * @param map
     * @param out
     */
	public static void writeOBJNOTEString(Map map, Writer out) throws IOException {
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
			Map.Entry entry=(Map.Entry)iter.next();
            out.write('\"');
            out.write(escape(String.valueOf(entry.getKey())));
            out.write('\"');
            out.write(':');
			OBJNOTECore.writeOBJNOTEString(entry.getValue(), out);
		}
		out.write('}');
	}

	public void writeOBJNOTEString(Writer out) throws IOException{
		writeOBJNOTEString(this, out);
	}
	
	/**
	 * Convert a map to JSON text. The result is a JSON object. 
	 * If this map is also a JSONAware, JSONAware specific behaviours will be omitted at this top level.
	 * 
	 * @see OBJNOTECore#toOBJNOTEString(Object)
	 * 
	 * @param myMap
	 * @return JSON text, or "null" if map is null.
	 */
	public static String toOBJNOTEString(Map myMap){
		@Bound("+ 2 (* 6 myMap)") int i;
		if(myMap == null)
			return "null";
		
        @Inv("= (- sb iter iter iter iter iter iter) (- (+ c97 c102 c105 c107 c110 c111 c112 c114) c104 c104 c104 c104 c104 c104)") StringBuffer sb = new StringBuffer();
        boolean first = true;
		@Iter("<= iter myMap") Iterator<Map.Entry> iter = myMap.entrySet().iterator();
		
        c97: sb.append('{');
		while(iter.hasNext()){
            if(first)
                first = false;
            else
                c102: sb.append(',');
			Map.Entry entry;
			c104: entry = iter.next();
			c105: sb.append('\"');
			String key = String.valueOf(entry.getKey());
			Object core = entry.getValue();
			if(key == null)
				c107: sb.append("null");
			else
				OBJNOTECore.escape(key, sb);
			c110: sb.append('\"');
			c111: sb.append(':');
			c112: sb.append(OBJNOTECore.toOBJNOTEString(core));
		}
        c114: sb.append('}');
		return sb.toString();
	}
	
	public String toOBJNOTEString(){
		return toOBJNOTEString(this);
	}
	
	public String toString(){
		return toOBJNOTEString();
	}

	public static String toString(String key,Object core){
		@Bound("5") int i;
        @Inv("= sb (+ c130 c132 c135 c136 c138)") StringBuffer sb = new StringBuffer();
		c130: sb.append('\"');
		if(key == null)
			c132: sb.append("null");
		else
			OBJNOTECore.escape(key, sb);
		c135: sb.append('\"');
		c136: sb.append(':');

		c138: sb.append(OBJNOTECore.toOBJNOTEString(core));
        return sb.toString();
	}
	
	/**
	 * Escape quotes, \, /, \r, \n, \b, \f, \t and other control characters (U+0000 through U+001F).
	 * It's the same as JSONValue.escape() only for compatibility here.
	 * 
	 * @see OBJNOTECore#escape(String)
	 * 
	 * @param s
	 * @return
	 */
	public static String escape(String s){
		return OBJNOTECore.escape(s);
	}
}
