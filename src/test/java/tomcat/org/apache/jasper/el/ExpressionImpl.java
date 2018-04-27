/*
 * Licensed to the Apache Software Foundation (ASF) under one or more
 * contributor license agreements.  See the NOTICE file distributed with
 * this work for additional information regarding copyright ownership.
 * The ASF licenses this file to You under the Apache License, Version 2.0
 * (the "License"); you may not use this file except in compliance with
 * the License.  You may obtain a copy of the License at
 *
 *      http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */
package tomcat.org.apache.jasper.el;

import tomcat.javax.el.ELContext;
import tomcat.javax.el.ExpressionFactory;
import tomcat.javax.el.ValueExpression;
import tomcat.javax.servlet.jsp.el.ELException;
import tomcat.javax.servlet.jsp.el.Expression;
import tomcat.javax.servlet.jsp.el.VariableResolver;

@Deprecated
public final class ExpressionImpl extends Expression {

    private final ValueExpression ve;
    private final ExpressionFactory factory;


    public ExpressionImpl(ValueExpression ve, ExpressionFactory factory) {
        this.ve = ve;
        this.factory = factory;
    }

    @Override
    public Object evaluate(VariableResolver vResolver) throws ELException {
        ELContext ctx =
                new ELContextImpl(new ELResolverImpl(vResolver, factory));
        return ve.getValue(ctx);
    }
}
