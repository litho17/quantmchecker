/*
 * $Id: Yytoken.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package braidit_1.com.cyberpointllc.stac.jack.direct.grabber;

import plv.colorado.edu.quantmchecker.qual.Inv;

/**
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class Yytoken {
	public static final int TYPE_CORE =0;//JSON primitive value: string,number,boolean,null
	public static final int TYPE_FIRST_BRACE =1;
	public static final int TYPE_TWO_BRACE =2;
	public static final int TYPE_FIRST_SQUARE =3;
	public static final int TYPE_TWO_SQUARE =4;
	public static final int TYPE_COMMA=5;
	public static final int TYPE_COLON=6;
	public static final int TYPE_EOF=-1;//end of file
	
	public int type=0;
	public Object core =null;
	
	public Yytoken(int type,Object core){
		this.type=type;
		this.core = core;
	}
	
	public String toString(){
		@Inv("= self (+ c34 c35 c36 c39 c42 c45 c51 c54 c57)") StringBuffer sb = new StringBuffer();
		switch(type){
		case TYPE_CORE:
			c34: sb.append("VALUE(");
			c35: sb.append(core);
			c36: sb.append(")");
			break;
		case TYPE_FIRST_BRACE:
			c39: sb.append("LEFT BRACE({)");
			break;
		case TYPE_TWO_BRACE:
			c42: sb.append("RIGHT BRACE(})");
			break;
		case TYPE_FIRST_SQUARE:
			c45: sb.append("LEFT SQUARE([)");
			break;
		case TYPE_TWO_SQUARE:
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
