using JuMP, CPLEX

function readFile(sfile)

   inst = open(sfile,"r")
   s = read(inst,String)
   close(inst)

   s = parse.(Int,split(s))

   n = s[1]

   jogo = zeros(Int,n,n)
   k = 2
   for i=1:n
      jogo[i,:] = s[k:k+n-1]
      k += n
   end

   return n, jogo
end

# ======================================

function buildModel(n,jogo)

   C = Vector{Array{Int64,2}}[]

   m = zeros(Int,n,n)

   nk = true                 # identifica as celulas repetidas nas linhas
   for i = 1 : n
      for j = 1 : n
         if m[i,j] == 1 
            continue
         end
         if nk 
            push!(C,Array{Int64,2}[]) 
            nk = false
         end
         for k = j+1 : n
            if jogo[i,j] == jogo[i,k] 
               m[i,k] = 1
               push!(C[end],[i k])  
               nk = true
            end
         end
         if nk 
            m[i,j] = 1
            push!(C[end],[i j])
         end
      end
   end

   if length(C[end]) == 0 
      nk = false # identifica as celulas repetidas nas linhas
   else
      nk = true
   end
   for j = 1 : n
      for i = 1 : n
         if m[i,j] == 2 
            continue
         end
         if nk 
            push!(C,Array{Int64,2}[]) 
            nk = false
         end
         for k = i+1 : n
            if jogo[i,j] == jogo[k,j] 
               m[k,j] = 2
               push!(C[end],[k j])  
               nk = true
            end
         end
         if nk 
            m[i,j] = 2
            push!(C[end],[i j])
         end
      end
   end

   if length(C[end]) > 0 
      push!(C,Array{Int64,2}[]) 
   end
 
   model = Model(with_optimizer(CPLEX.Optimizer, CPX_PARAM_TILIM=1800))  #CPX_PARAM_SCRIND=false, 

   @variable(model, x[i = 1:n, j = 1:n], Bin)  

   @objective(model,Min,sum(x[i,j] for i = 1:n for j = 1:n if  m[i,j] > 0))

  # =====================================  Restricao Sombrear celulas com nros repetidos ===========================
   
   for i = 1 : length(C)-1
      ex = AffExpr()
      for j = 1 : length(C[i])
         add_to_expression!(ex, 1.0, x[C[i][j][1],C[i][j][2]])
      end
      @constraint(model, ex >= length(C[i])-1)
   end

  # =====================================  Restricao Vizinhos Ortogonais ===========================================
   for i = 1 : n
      for j = 1 : n
         if m[i,j] > 0
            if( j + 1 <= n && m[i,j+1] > 0) 
               @constraint(model,x[i,j] + x[i,j+1] <= 1)
            end
            if( i + 1 <= n && m[i+1,j] > 0) 
               @constraint(model,x[i,j] + x[i+1,j] <= 1)
            end
         end
      end
   end

# =====================================  Restricao continuidade area com celulas nao sombreadas =======================================
   fonte = [ 0 0 ]
   for i = 1 : n
      for j = 1 : n
         if m[i,j] == 0
            fonte = [i j]
            break
         end
      end
      if fonte[1] > 0
         break
      end
   end
   
   @variable(model, y[i = 1:n,   j = 1:n, il = i-1 : i+1, jl = j-1 : j+1 ] >= 0)  
   
   ex = AffExpr()
   if fonte[1] > 1  
      add_to_expression!(ex, 1.0, y[fonte[1],fonte[2],fonte[1]-1,fonte[2]] )
   end
   if fonte[1] < n  
      add_to_expression!(ex, 1.0, y[fonte[1],fonte[2],fonte[1]+1,fonte[2]] )
   end
   if fonte[2] > 1  
      add_to_expression!(ex, 1.0, y[fonte[1],fonte[2],fonte[1],fonte[2]-1] )
   end
   if fonte[2] < n  
      add_to_expression!(ex, 1.0, y[fonte[1],fonte[2],fonte[1],fonte[2]+1] )
   end

   @constraint(model, ex >= n^2 - 1 - sum((m[i,j] > 0) * x[i,j] for i = 1:n for j = 1:n)) 

   for i = 1 : n
      for j = 1 : n
         if i == fonte[1] && j == fonte[2]
            continue
         end
         ex = AffExpr()
         if i > 1 
            add_to_expression!(ex,1.0,y[i-1,j,i,j])
            if i-1 != fonte[1] || j != fonte[2]
               add_to_expression!(ex,-1.0,y[i,j,i-1,j])
            end
         end
         if i < n  
            add_to_expression!(ex,1.0,y[i+1,j,i,j])
            if i+1 != fonte[1] || j != fonte[2]
               add_to_expression!(ex,-1.0,y[i,j,i+1,j])
            end
         end
         if j > 1 
            add_to_expression!(ex,1.0,y[i,j-1,i,j])
            if j-1 != fonte[2] || i != fonte[1]
               add_to_expression!(ex,-1.0,y[i,j,i,j-1])
            end
         end
         if j < n 
            add_to_expression!(ex,1.0,y[i,j+1,i,j])
            if j+1 != fonte[2] || i != fonte[1]
               add_to_expression!(ex,-1.0,y[i,j,i,j+1])
            end 
         end
         @constraint(model, ex ==  1 - (m[i,j] > 0) * x[i,j]) 
      end
   end

   for i = 1 : n
      for j = 1 : n
         if  m[i,j] > 0 
            ex = AffExpr()
            if i > 1 
               add_to_expression!(ex,1.0,y[i-1,j,i,j])
            end
            if i < n  
               add_to_expression!(ex,1.0,y[i+1,j,i,j])
            end
            if j > 1 
               add_to_expression!(ex,1.0,y[i,j-1,i,j])
            end
            if j < n 
               add_to_expression!(ex,1.0,y[i,j+1,i,j])
            end
            @constraint(model, ex <= n^2 * (1 - x[i,j]))
         end
      end
   end
   
   open("model.lp", "w") do f
      print(f, model)
   end

   JuMP.optimize!(model)

   tableau = zeros(Int,n,n) 
   for i = 1 : n
      for j =  1 : n
         if JuMP.value(x[i,j]) > 0.5 
            println("x[$i,$j] = ",JuMP.value(x[i,j]))
            tableau[i,j] = 1
         end
      end
   end
  
   conta  = checkSolu(tableau)
   if conta == 0
      println("Solucao ok")
   else
      println("$conta celulas ilhadas")
   end


end
# ======================================
function checkSolu(tableau)
   n = length(tableau[:,1])
   i = 1
   j = 1

   while tableau[i,j] > 0 
      j += 1
      if j > n 
         i += 1
         j = 1
      end
   end   

   verificaViz(tableau,n,i,j)

   ok = 0  
   for i = 1 : n 
      for j = 1 : n
         if tableau[i,j] == 0
            ok += 1
         end
      end
   end

   return ok
end

# =========================
function verificaViz(tableau,n,i,j)
   if tableau[i,j] == 0
      tableau[i,j] = 1
      if  i - 1 > 0 
         verificaViz(tableau,n,i-1,j)
      end
      if  i + 1 <= n 
         verificaViz(tableau,n,i+1,j)
      end
      if  j - 1 > 0 
         verificaViz(tableau,n,i,j-1)
      end
      if  j + 1 <= n 
         verificaViz(tableau,n,i,j+1)
      end
   end
end

# =========================


n,jogo = readFile(ARGS[1])


buildModel(n,jogo)

