
install.packages("ape")
install.packages("phangorn")
install.packages("OUwie")
install.packages("mvtnorm")
library(ape)
library(phangorn)
library(OUwie)
library(mvtnorm)

#######################Need to set wd and 
#get or create genetic and trait data################


######################Functions#################
##################Function to compute compatibility matrix######################
compatibility <- function(a,m){
  compatibility.mat <- matrix(0,ncol(a), 1)
  for(i in 1:(ncol(a))){
      has.00 <- 0
      has.01 <- 0
      has.10 <- 0
      has.11 <- 0
      for(k in 1:nrow(a)){
        if(a[k,i]== "0" &&a[k,m]=="0"){
          has.00 <- 1
        }else if(a[k,i]=="0" && a[k,m]=="1"){
          has.01 <- 1
        }else if (a[k,i]=="1" && a[k,m]=="0"){
          has.10 <- 1
        }else{
          has.11 <- 1
        }
      }
      if(has.00+has.01+has.10+has.11 < 4){
        compatibility.mat[i] <- 1
      }
    }
  
  return(compatibility.mat)
}


#########################Function to get all neighboring ones###########


order <- function(i, comp){
  ones <- i
  j <- 1
  SNP.0L <- FALSE
  SNP.0R <- FALSE
  n <- length(comp)
  compat <- comp
  ############################Tracking Down Neighboring Ones#############
  while(SNP.0L == FALSE){
    if(i-j==0){
      SNP.0L <- TRUE
    }else{
      if(compat[i-j]==0){
        SNP.0L <- TRUE
      }else{
        ones <- c(ones, i-j)
        j <- j+1
      }
    }
  }
  j <- 1
  while(SNP.0R==FALSE){
    if(i+j==n+1){
      SNP.0R <- TRUE
    }else{
      if(compat[i+j]==0){
        SNP.0R <- TRUE
      }else{
        ones <- c(ones, i+j)
        j <- j+1
      }
    }
  }
  ones.left <- ones[(1:length(ones))[ones < i]]
  ones.right <- ones[(1:length(ones))[ones > i]]
  ord <- i
  l1 <- length(ones.left)
  l2 <- length(ones.right)
  if(l1==0){
    ord <- c(ord, ones.right)
  }else if(l2==0){
    ord <- c(ord, ones.left)
  }else{
    for(k in 1:min(l1,l2)){
      ord <- c(ord, ones.left[k], ones.right[k])
    }
    if(l1 < l2){
      ord <- c(ord, ones.right[(l1+1):l2])
    }else if(l2 < l1){
      ord <- c(ord,ones.left[(l2+1):l1])
    }
  }
  a <- seq(1,n,1)
  left <- a[(1:length(a))[a < min(ord)]]
  right <- a[(1:length(a))[a > max(ord)]]
  left <- sort(left, decreasing=TRUE)
  l1 <- length(left)
  l2 <- length(right)
  if(l1==0){
    ord <- c(ord, right)
  }else if(l2==0){
    ord <- c(ord, left)
  }else{
    for(k in 1:min(l1, l2)){
      ord <- c(ord, left[k], right[k])
    }
    if(l1 < l2){
      ord <- c(ord, right[(l1+1):l2])
    }else if(l2 < l1){
      ord <- c(ord, left[(l2+1):l1])
    }
  }
  return(ord)
}

#################################Function to Build Tree Edge Matrix##################
pph <- function(data, i){
  ##############################Initializing Edge Matrix#############################
  comp <- compatibility(data, i)
  ord <- order(i,comp)
  nleaves <- nrow(data)
  edges <- matrix(NA, 2*nleaves-2, 4)
  child.leaves <- matrix(NA, nleaves-1, nleaves)
  child.leaves[1,] <- 1:nleaves
  site <- 1
  pos <- 1
  res.tree <- FALSE
  next.gen.nodes <- nleaves+1
  not.both <- TRUE
  while(not.both == TRUE){
    children <- NULL
    tip.labels <- NULL
    SNP <- data[,ord[site]]
    edges[1,4] <- 1
    for(k in next.gen.nodes){
      parent <- k
      leaves <- which(is.na(child.leaves[k-nleaves, ]) == FALSE, arr.ind=FALSE)
      desc.leaves <- child.leaves[k-nleaves, leaves]
      ########################Split by 0's and 1's####################
      zeroes <- NULL
      ones <- NULL
      for(m in desc.leaves){
        
        if(SNP[m]=="0"){
          zeroes <- c(zeroes, m)
        }else{
          ones <- c(ones, m)
        }
      }
      #######################Figuring out new descendants##############
      nleft <- length(zeroes)
      nright <- length(ones)
      if(nleft==0||nright==0){
        children <- c(children, k)
        not.both <- TRUE
        site <- site+1
        edges[1,4] <- edges[1,4] + 1
        
      }else{
        not.both <- FALSE
        if(nleft==1){
          pos2 <- pos+2
          edges[pos,1] <- parent
          edges[pos,3] <- zeroes[1]
          right.child <- parent+1
        }else if(nleft==2){
          left.child <- parent+1
          edges[pos,1:2] <- c(parent, left.child)
          edges[pos+1, 1] <- left.child
          edges[pos+1,3] <- zeroes[1]
          edges[pos+2, 1] <- left.child
          edges[pos+2,3] <- zeroes[2]
          child.leaves[left.child-nleaves, 1:nleft] <- zeroes
          
        }else if(nleft > 2){
          left.child <- parent+1
          edges[pos,1:2] <- c(parent, left.child)
          children <- c(children, left.child)
          child.leaves[left.child-nleaves, 1:nleft] <- zeroes
          
        }
        pos2 <- pos+2*nleft-1
        if(nright==1){
          edges[pos2, 1] <- parent
          edges[pos2,3] <- ones[1]
        }else if(nright==2){
          right.child <- parent+nleft
          edges[pos2,1:2] <- c(parent, right.child)
          edges[pos2+1,1] <- right.child
          edges[pos2+1,3] <- ones[1]
          edges[pos2+2,1] <- right.child
          edges[pos2+2,3] <- ones[2]
          child.leaves[right.child-nleaves, 1:nright] <- ones
          
        }else if(nright > 2){
          right.child <- parent+nleft
          edges[pos2,1:2] <- c(parent,right.child)
          children <- c(children, right.child)
          child.leaves[right.child-nleaves, 1:nright] <- ones
          
        }
      }
    }
  }
  
  next.gen.nodes <- children
  
  res.tree <- FALSE
  num.sites <- ncol(data)
  while(res.tree == FALSE && site <= num.sites){
    children <- NULL
    tip.labels <- NULL
    SNP <- data[,ord[site]]
    for(k in next.gen.nodes){
      parent <- k
      pos <- which(edges[,2]==parent, arr.ind=TRUE)
      leaves <- which(is.na(child.leaves[k-nleaves, ]) == FALSE, arr.ind=FALSE)
      desc.leaves <- child.leaves[k-nleaves, leaves]
      ########################Split by 0's and 1's####################
      zeroes <- NULL
      ones <- NULL
      for(m in desc.leaves){
        
        if(SNP[m]==0){
          zeroes <- c(zeroes, m)
        }else{
          ones <- c(ones, m)
        }
      }
      #######################Figuring out new descendants##############
      nleft <- length(zeroes)
      nright <- length(ones)
      if(nleft==0||nright==0){
        children <- c(children, k)
      }else{
        if(nleft==1){
          pos2 <- pos+2
          edges[pos+1,1] <- parent
          edges[pos+1,3] <- zeroes[1]
          right.child <- parent+1
        }else if(nleft==2){
          left.child <- parent+1
          edges[pos+1,1:2] <- c(parent, left.child)
          edges[pos+2, 1] <- left.child
          edges[pos+2,3] <- zeroes[1]
          edges[pos+3, 1] <- left.child
          edges[pos+3,3] <- zeroes[2]
          child.leaves[left.child-nleaves, 1:nleft] <- zeroes
          
        }else if(nleft > 2){
          left.child <- parent+1
          edges[pos+1,1:2] <- c(parent, left.child)
          children <- c(children, left.child)
          child.leaves[left.child-nleaves, 1:nleft] <- zeroes
          
        }
        pos2 <- pos+2*nleft
        if(nright==1){
          edges[pos2, 1] <- parent
          edges[pos2, 3] <- ones[1]
        }else if(nright==2){
          right.child <- parent+nleft
          edges[pos2,1:2] <- c(parent, right.child)
          edges[pos2+1,1] <- right.child
          edges[pos2+1,3] <- ones[1]
          edges[pos2+2,1] <- right.child
          edges[pos2+2,3] <- ones[2]
          child.leaves[right.child-nleaves, 1:nright] <- ones
          
        }else if(nright > 2){
          right.child <- parent+nleft
          edges[pos2,1:2] <- c(parent,right.child)
          children <- c(children, right.child)
          child.leaves[right.child-nleaves, 1:nright] <- ones
          
        }
      }
      
      
    }
    ##########################Is Tree Resolved?##########################
    res.tree <- TRUE
    for(r in 1:nrow(edges)){
      if(is.na(edges[r,1])){
        res.tree <- FALSE
        site <- site+1
        edges[1,4] <- edges[1,4] + 1
        break
      }
    }
    next.gen.nodes <- children
  }
  if(res.tree == FALSE){
    stop("Tree Cannot Be Fully Resolved")
  }else{
    nas <- which(is.na(edges[,2]))
    edges[nas,2] <- 1:nleaves
    tip.labels <- edges[which(is.na(edges[,3])==FALSE), 3]
  }
  
  return(edges)
}

#################Function to convert edge matrix to tree########
convert.to.tree <- function(data, edges){
  nleaves <- nrow(data)
  init.tree <- rtree(nleaves, rooted=TRUE, br=NULL)
  init.tree$edge <- edges[,1:2]
  tree <- init.tree
  return(tree)
  
}

#########################################################################
#########################################################################
############################Gibbs Sampler to Compute Posterior Density Ratio
#########################################################################
#########################################################################

############################Specifying Prior Parameters##################
alpha.prior <- 1
beta <- 1
sigma0.2 <- 1
I <- matrix(0, tips, tips)
for(i in 1:tips){
	I[i,i] <- 1
}

#############################Functions for Posterior Parameters###################################
alpha.post <- alpha.prior + tips/2

beta.post <- function(a,b,c){
	beta + 0.5*t(a-b)%*%c%*%(a-b)
}

post.mean <- function(a,b,c,d){
	solve(1/sigma0.2*I + 1/a*c)%*%(1/sigma0.2*d + 1/a*c%*%b)
}

post.cov <- function(a,b){
	solve(1/sigma0.2*I + 1/a*b)
}

k <- tips+1

BIC <- function(a,b,c,d){
	k*log(tips) + tips/2*log(2*pi*a)+1/a*t(b-d)%*%c%*%(b-d)
}
captured <- NULL
##############################Initialize Sampler#############################
BIC.vec <- NULL
num.iterations <- 5000

##############################################################################
##############################################################################
###############################SNP Detection##################################
##############################################################################
##############################################################################
BIC.vec.det <- NULL
BIC.stats <- NULL



log.post.vec <- NULL
for(m in 1:ncol(data.matrix)){
	site <- m
	##########################Specifying Prior Mean#################
	mu.0 <- NULL
	for(i in 1:nrow(data.matrix)){
		if(data.matrix[i,m] == "0"){
			mu.0 <- c(mu.0, theta.1)
		}else{
			mu.0 <- c(mu.0, theta.2)
		}
	}
	#################################################################
	
	##########################Building Tree##########################
	comp <- compatibility(data.matrix, site)
	ord <- order(site, comp)
	edge <- pph(data.matrix, site)
	snps.to.use <- ord[1:edge[1,4]]
	tree <- convert.to.tree(data.matrix, edge)
	tip.labels <- edge[which(is.na(edge[,3])==FALSE), 3]
	tree$tip.label <- tip.labels

############Ordering mu.0 and trait values#########################
	compare <- as.numeric(rownames(data.matrix))
	mu.0.ord <- NULL
	trait.ord <- NULL
	for(i in tip.labels){
		for(j in 1:length(compare)){
			if(i==compare[j]){
				mu.0.ord <- c(mu.0.ord, mu.0[j])
				trait.ord <- c(trait.ord, trait.vals[j])
				break
			}
			
		}
	}

################Getting SNPs we are going to use#################
	data.use <- data.matrix[,snps.to.use]
	data.use <- as.phyDat(data.use, type="USER", levels=c("0", "1"))

###########Maximum Likelihood Branch Lengths#########
	tree <- compute.brtime(tree, method="coalescent")
	like <- pml(tree, data.use)
	ml.tree <- optim.pml(like, optNni=FALSE, optEdge=TRUE, optRooted=TRUE)
	tree <- ml.tree$tree
	dist.tree <- dist.nodes(tree)
	tree$edge.length <- 2*tree$edge.length/max(dist.tree)

############Covariance Matrix########################

cov <- matrix(0, tips, tips)
root <- tips+1
distances <- dist.nodes(tree)[root,]

for(i in 1:(tips-1)){
	for(j in (i+1):tips){
		ancestor <- getMRCA(tree, c(i,j))
		cov[i,j] <- distances[ancestor]
		cov[j,i] <- cov[i,j]
	}
}
for(i in 1:tips){
	cov[i,i] <- 4*distances[i]
}

V.inv <- solve(cov)
trait.ord <- as.matrix(trait.ord)
mus <- NULL
sigma2s <- NULL
mu <- mu.0.ord
for(l in 1:num.iterations){
	sigma.2 <- 1/rgamma(1, alpha.post, beta.post(mu,trait.ord,V.inv))
	mu <- t(rmvnorm(1, post.mean(sigma.2, trait.ord, V.inv, mu.0.ord), post.cov(sigma.2, V.inv)))
	mus <- cbind(mus, mu)
	sigma2s <- c(sigma2s, sigma.2)
}  
mu.hat <- NULL
for(i in 1:tips){
	mu.hat <- c(mu.hat, mean(mus[i,]))
}
sigma2.hat <- mean(sigma2s)
post.covar <- post.cov(sigma2.hat, V.inv)
inv.covar <- solve(post.covar)
post.mean.vec <- post.mean(sigma2.hat, trait.ord, V.inv, mu.0.ord)
log.post <- -0.5*log(det(2*pi*post.covar)) - 0.5*t(mu.hat-post.mean.vec)%*%V.inv%*%(mu.hat-post.mean.vec) - (M/2-alpha.prior-1)*log(sigma2.hat)-1/sigma2.hat*(1/beta + 0.5*t(trait.ord-mu.hat)%*%V.inv%*%(trait.ord-mu.hat))
log.post.vec <- c(log.post.vec, log.post)

}

##########################Do we pick up the disease locus?#####################

##################Matrix of Posterior Odds Ratios################
post.odds.mat <- matrix(0, N, N)
for(i in 1:(N-1)){
	for(j in i:N){
		post.odds.mat[i,j] <- exp(log.post.vec[i]-log.post.vec[j])
		post.odds.mat[j,i] <- 1/post.odds.mat[i,j]
	}
}

###################Checking to see if we caught disease locus#######
props <- NULL
for(i in 1:N){
	prop <- 0
		for(j in 1:N){
			if(post.odds.mat[i,j] >= 3){
				prop <- prop+1/N
			}
		}
		props <- c(props, prop)
}	
prop.sort <- sort(props)
if(props[disease.locus] >= prop.sort[0.95*length(prop.sort)]){
	caught <- c(caught, 1)
}else{
	caught <- c(caught, 0)
}

print(z)
}
	