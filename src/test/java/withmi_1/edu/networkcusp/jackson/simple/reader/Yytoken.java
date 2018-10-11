/*
 * $Id: Yytoken.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package withmi_1.edu.networkcusp.jackson.simple.reader;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class Yytoken {
	public static final int TYPE_VALUE=0;//JSON primitive value: string,number,boolean,null
	public static final int TYPE_LEFT_BRACE=1;
	public static final int TYPE_RIGHT_BRACE=2;
	public static final int TYPE_LEFT_SQUARE=3;
	public static final int TYPE_RIGHT_SQUARE=4;
	public static final int TYPE_COMMA=5;
	public static final int TYPE_COLON=6;
	public static final int TYPE_EOF=-1;//end of file
	
	public int type=0;
	public Object value=null;
	
	public Yytoken(int type,Object value){
		this.type=type;
		this.value=value;
	}
	
	public String toString(){
		@Bound("3") int i;
		@Inv("= sb (+ c36 c37 c38 c41 c44 c47 c50 c53 c56 c59)") StringBuffer sb = new StringBuffer();
		switch(type){
		case TYPE_VALUE:
			c36: sb.append("VALUE(");
			c37: sb.append(value);
			c38: sb.append(")");
			break;
		case TYPE_LEFT_BRACE:
			c41: sb.append("LEFT BRACE({)");
			break;
		case TYPE_RIGHT_BRACE:
			c44: sb.append("RIGHT BRACE(})");
			break;
		case TYPE_LEFT_SQUARE:
			c47: sb.append("LEFT SQUARE([)");
			break;
		case TYPE_RIGHT_SQUARE:
			c50: sb.append("RIGHT SQUARE(])");
			break;
		case TYPE_COMMA:
			c53: sb.append("COMMA(,)");
			break;
		case TYPE_COLON:
			c56: sb.append("COLON(:)");
			break;
		case TYPE_EOF:
			c59: sb.append("END OF FILE");
			break;
		}
		return sb.toString();
	}
}
