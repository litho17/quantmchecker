/*
 * $Id: JSONParser.java,v 1.1 2006/04/15 14:10:48 platform Exp $
 * Created on 2006-4-15
 */
package braidit_1.com.cyberpointllc.stac.jack.direct.grabber;

import braidit_1.com.cyberpointllc.stac.jack.direct.OBJNOTEArray;
import braidit_1.com.cyberpointllc.stac.jack.direct.OBJNOTEObject;
import plv.colorado.edu.quantmchecker.qual.InvUnk;

import java.io.IOException;
import java.io.Reader;
import java.io.StringReader;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;


/**
 * Parser for JSON text. Please note that JSONParser is NOT thread-safe.
 * 
 * @author FangYidong<fangyidong@yahoo.com.cn>
 */
public class OBJNOTEParser {
	public static final int S_INIT=0;
	public static final int S_IN_FINISHED_CORE =1;//string,number,boolean,null,object,array
	public static final int S_IN_OBJECT=2;
	public static final int S_IN_ARRAY=3;
	public static final int S_PASSED_PAIR_KEY=4;
	public static final int S_IN_PAIR_CORE =5;
	public static final int S_END=6;
	public static final int S_IN_ERROR=-1;
	
	private LinkedList managerStatusStack;
	private Yylex lexer = new Yylex((Reader)null);
	private Yytoken token = null;
	private int status = S_INIT;
	
	private int peekStatus(LinkedList statusStack){
		if(statusStack.size()==0)
			return -1;
		Integer status=(Integer)statusStack.getFirst();
		return status.intValue();
	}
	
    /**
     *  Reset the parser to the initial state without resetting the underlying reader.
     *
     */
    public void reset(){
        token = null;
        status = S_INIT;
        managerStatusStack = null;
    }
    
    /**
     * Reset the parser to the initial state with a new character reader.
     * 
     * @param in - The new character reader.
     * @throws IOException
     * @throws ParseException
     */
	public void reset(Reader in){
		lexer.yyreset(in);
		reset();
	}
	
	/**
	 * @return The position of the beginning of the current token.
	 */
	public int pullPosition(){
		return lexer.fetchPosition();
	}
	
	public Object parse(String s) throws ParseException{
		return parse(s, (ContainerFactory)null);
	}
	
	public Object parse(String s, ContainerFactory containerFactory) throws ParseException{
		StringReader in=new StringReader(s);
		try{
			return parse(in, containerFactory);
		}
		catch(IOException ie){
			/*
			 * Actually it will never happen.
			 */
			throw new ParseException(-1, ParseException.ERROR_UNEXPECTED_EXCEPTION, ie);
		}
	}
	
	public Object parse(Reader in) throws IOException, ParseException{
		return parse(in, (ContainerFactory)null);
	}
	
	/**
	 * Parse JSON text into java object from the input source.
	 * 	
	 * @param in
     * @param containerFactory - Use this factory to createyour own JSON object and JSON array containers.
	 * @return Instance of the following:
	 *  org.json.simple.JSONObject,
	 * 	org.json.simple.JSONArray,
	 * 	java.lang.String,
	 * 	java.lang.Number,
	 * 	java.lang.Boolean,
	 * 	null
	 * 
	 * @throws IOException
	 * @throws ParseException
	 */
	public Object parse(Reader in, ContainerFactory containerFactory) throws IOException, ParseException{
		reset(in);
		@InvUnk("Complex loop") LinkedList statusStack = new LinkedList();
		@InvUnk("Complex loop") LinkedList coreStack = new LinkedList();
		
		try{
			do{
				ensuingToken();
				switch(status){
				case S_INIT:
					switch(token.type){
					case Yytoken.TYPE_CORE:
						status= S_IN_FINISHED_CORE;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(token.core);
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(composeObjectContainer(containerFactory));
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(composeArrayContainer(containerFactory));
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_CORE:
					if(token.type==Yytoken.TYPE_EOF)
						return coreStack.removeFirst();
					else
						throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
					
				case S_IN_OBJECT:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_CORE:
						if(token.core instanceof String){
							String key=(String)token.core;
							coreStack.addFirst(key);
							status=S_PASSED_PAIR_KEY;
							statusStack.addFirst(new Integer(status));
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_TWO_BRACE:
						if(coreStack.size()>1){
							parseExecutor(statusStack, coreStack);
						}
						else{
							status= S_IN_FINISHED_CORE;
						}
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_CORE:
						statusStack.removeFirst();
						String key=(String) coreStack.removeFirst();
						@InvUnk("Read from nested list") Map parent=(Map) coreStack.getFirst();
						parent.put(key,token.core);
						status=peekStatus(statusStack);
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						statusStack.removeFirst();
						key=(String) coreStack.removeFirst();
						parent=(Map) coreStack.getFirst();
						@InvUnk("Interface return list") List newArray= composeArrayContainer(containerFactory);
						parent.put(key,newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(newArray);
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						statusStack.removeFirst();
						key=(String) coreStack.removeFirst();
						parent=(Map) coreStack.getFirst();
						@InvUnk("Interface return list") Map newObject= composeObjectContainer(containerFactory);
						parent.put(key,newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(newObject);
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
					
				case S_IN_ARRAY:
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_CORE:
						List val=(List) coreStack.getFirst();
						val.add(token.core);
						break;
					case Yytoken.TYPE_TWO_SQUARE:
						if(coreStack.size()>1){
							new OBJNOTEParserWorker(statusStack, coreStack).invoke();
						}
						else{
							status= S_IN_FINISHED_CORE;
						}
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						val=(List) coreStack.getFirst();
						@InvUnk("Interface return list") Map newObject= composeObjectContainer(containerFactory);
						val.add(newObject);
						status=S_IN_OBJECT;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(newObject);
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						val=(List) coreStack.getFirst();
						List newArray= composeArrayContainer(containerFactory);
						val.add(newArray);
						status=S_IN_ARRAY;
						statusStack.addFirst(new Integer(status));
						coreStack.addFirst(newArray);
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
				case S_IN_ERROR:
					throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			throw ie;
		}
		
		throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseExecutor(LinkedList statusStack, LinkedList coreStack) {
		statusStack.removeFirst();
		coreStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private void ensuingToken() throws ParseException, IOException{
		token = lexer.yylex();
		if(token == null)
			token = new Yytoken(Yytoken.TYPE_EOF, null);
	}
	
	private Map composeObjectContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new OBJNOTEObject();
		@InvUnk("Interface return list") Map m = containerFactory.composeObjectContainer();
		
		if(m == null)
			return new OBJNOTEObject();
		return m;
	}
	
	private List composeArrayContainer(ContainerFactory containerFactory){
		if(containerFactory == null)
			return new OBJNOTEArray();
		@InvUnk("Interface return list") List l = containerFactory.creatArrayContainer();
		
		if(l == null)
			return new OBJNOTEArray();
		return l;
	}
	
	public void parse(String s, ContentManager contentManager) throws ParseException{
		parse(s, contentManager, false);
	}
	
	public void parse(String s, ContentManager contentManager, boolean isResume) throws ParseException{
		StringReader in=new StringReader(s);
		try{
			parse(in, contentManager, isResume);
		}
		catch(IOException ie){
			/*
			 * Actually it will never happen.
			 */
			throw new ParseException(-1, ParseException.ERROR_UNEXPECTED_EXCEPTION, ie);
		}
	}
	
	public void parse(Reader in, ContentManager contentManager) throws IOException, ParseException{
		parse(in, contentManager, false);
	}
	
	/**
	 * Stream processing of JSON text.
	 * 
	 * @see ContentManager
	 * 
	 * @param in
	 * @param contentManager
	 * @param isResume - Indicates if it continues previous parsing operation.
     *                   If set to true, resume parsing the old stream, and parameter 'in' will be ignored. 
	 *                   If this method is called for the first time in this instance, isResume will be ignored.
	 * 
	 * @throws IOException
	 * @throws ParseException
	 */
	public void parse(Reader in, ContentManager contentManager, boolean isResume) throws IOException, ParseException{
		if(!isResume){
			reset(in);
			managerStatusStack = new LinkedList();
		}
		else{
			if(managerStatusStack == null){
				isResume = false;
				reset(in);
				managerStatusStack = new LinkedList();
			}
		}
		
		try{
			do{
				switch(status){
				case S_INIT:
					contentManager.startOBJNOTE();
					ensuingToken();
					switch(token.type){
					case Yytoken.TYPE_CORE:
						status= S_IN_FINISHED_CORE;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.primitive(token.core))
							return;
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						status=S_IN_OBJECT;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						status=S_IN_ARRAY;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_IN_FINISHED_CORE:
					ensuingToken();
					if(token.type==Yytoken.TYPE_EOF){
						contentManager.endOBJNOTE();
						status = S_END;
						return;
					}
					else{
						status = S_IN_ERROR;
						throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
					}
			
				case S_IN_OBJECT:
					ensuingToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_CORE:
						if(token.core instanceof String){
							String key=(String)token.core;
							status=S_PASSED_PAIR_KEY;
							managerStatusStack.addFirst(new Integer(status));
							if(!contentManager.startObjectEntry(key))
								return;
						}
						else{
							status=S_IN_ERROR;
						}
						break;
					case Yytoken.TYPE_TWO_BRACE:
						if(managerStatusStack.size()>1){
							managerStatusStack.removeFirst();
							status=peekStatus(managerStatusStack);
						}
						else{
							status= S_IN_FINISHED_CORE;
						}
						if(!contentManager.endObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
						break;
					}//inner switch
					break;
					
				case S_PASSED_PAIR_KEY:
					ensuingToken();
					switch(token.type){
					case Yytoken.TYPE_COLON:
						break;
					case Yytoken.TYPE_CORE:
						managerStatusStack.removeFirst();
						status=peekStatus(managerStatusStack);
						if(!contentManager.primitive(token.core))
							return;
						if(!contentManager.endObjectEntry())
							return;
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						managerStatusStack.removeFirst();
						managerStatusStack.addFirst(new Integer(S_IN_PAIR_CORE));
						status=S_IN_ARRAY;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						managerStatusStack.removeFirst();
						managerStatusStack.addFirst(new Integer(S_IN_PAIR_CORE));
						status=S_IN_OBJECT;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}
					break;
				
				case S_IN_PAIR_CORE:
					/*
					 * S_IN_PAIR_VALUE is just a marker to indicate the end of an object entry, it doesn't proccess any token,
					 * therefore delay consuming token until next round.
					 */
					managerStatusStack.removeFirst();
					status = peekStatus(managerStatusStack);
					if(!contentManager.endObjectEntry())
						return;
					break;
					
				case S_IN_ARRAY:
					ensuingToken();
					switch(token.type){
					case Yytoken.TYPE_COMMA:
						break;
					case Yytoken.TYPE_CORE:
						if(!contentManager.primitive(token.core))
							return;
						break;
					case Yytoken.TYPE_TWO_SQUARE:
						if(managerStatusStack.size()>1){
							parseEntity(managerStatusStack);
						}
						else{
							status= S_IN_FINISHED_CORE;
						}
						if(!contentManager.endArray())
							return;
						break;
					case Yytoken.TYPE_FIRST_BRACE:
						status=S_IN_OBJECT;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startObject())
							return;
						break;
					case Yytoken.TYPE_FIRST_SQUARE:
						status=S_IN_ARRAY;
						managerStatusStack.addFirst(new Integer(status));
						if(!contentManager.startArray())
							return;
						break;
					default:
						status=S_IN_ERROR;
					}//inner switch
					break;
					
				case S_END:
					return;
					
				case S_IN_ERROR:
					throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
				}//switch
				if(status==S_IN_ERROR){
					throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
				}
			}while(token.type!=Yytoken.TYPE_EOF);
		}
		catch(IOException ie){
			status = S_IN_ERROR;
			throw ie;
		}
		catch(@InvUnk("Extend library class") ParseException pe){
			status = S_IN_ERROR;
			throw pe;
		}
		catch(RuntimeException re){
			status = S_IN_ERROR;
			throw re;
		}
		catch(Error e){
			status = S_IN_ERROR;
			throw e;
		}
		
		status = S_IN_ERROR;
		throw new ParseException(pullPosition(), ParseException.ERROR_UNEXPECTED_TOKEN, token);
	}

	private void parseEntity(LinkedList statusStack) {
		statusStack.removeFirst();
		status=peekStatus(statusStack);
	}

	private class OBJNOTEParserWorker {
		private LinkedList statusStack;
		private LinkedList coreStack;

		public OBJNOTEParserWorker(LinkedList statusStack, LinkedList coreStack) {
			this.statusStack = statusStack;
			this.coreStack = coreStack;
		}

		public void invoke() {
			statusStack.removeFirst();
			coreStack.removeFirst();
			status=peekStatus(statusStack);
		}
	}
}
