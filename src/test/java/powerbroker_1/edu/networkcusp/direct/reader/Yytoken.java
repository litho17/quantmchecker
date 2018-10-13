/*
 * $Id: Yytoken.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package powerbroker_1.edu.networkcusp.direct.reader;

import plv.colorado.edu.quantmchecker.qual.Bound;
import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class Yytoken {
	public static final int TYPE_DETAIL =0;//JSON primitive value: string,number,boolean,null
	public static final int TYPE_ONE_BRACE =1;
	public static final int TYPE_SECONDARY_BRACE =2;
	public static final int TYPE_ONE_SQUARE =3;
	public static final int TYPE_SECONDARY_SQUARE =4;
	public static final int TYPE_COMMA=5;
	public static final int TYPE_COLON=6;
	public static final int TYPE_EOF=-1;//end of file
	
	public int type=0;
	public Object detail =null;
	
	public Yytoken(int type,Object detail){
		this.type=type;
		this.detail = detail;
	}
	
	public String toString(){
		@Bound("3") int i;
		@Inv("= sb (+ c36 c37 c38 c39 c42 c45 c48 c51 c54 c57)") StringBuffer sb = new StringBuffer();
		switch(type){
		case TYPE_DETAIL:
			c36: sb.append("VALUE(");
			c37: sb.append(detail);
			c38: sb.append(")");
			break;
		case TYPE_ONE_BRACE:
			c39: sb.append("LEFT BRACE({)");
			break;
		case TYPE_SECONDARY_BRACE:
			c42: sb.append("RIGHT BRACE(})");
			break;
		case TYPE_ONE_SQUARE:
			c45: sb.append("LEFT SQUARE([)");
			break;
		case TYPE_SECONDARY_SQUARE:
			c48: sb.append("RIGHT SQUARE(])");
			break;
		case TYPE_COMMA:
			c51: sb.append("COMMA(,)");
			break;
		case TYPE_COLON:
			c54: sb.append("COLON(:)");
			break;
		case TYPE_EOF:
			c57: sb.append("END OF FILE");
			break;
		}
		return sb.toString();
	}
}
