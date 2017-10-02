node {
  def mvnHome = tool 'M3'
  env.JAVA_HOME="${tool 'jdk-oracle-8'}"
  env.PATH="${env.JAVA_HOME}/bin:${mvnHome}/bin:${env.PATH}"
  
  try {
    stage('Clone'){
      checkout scm
    }
    
    stage('Packaging') {
      sh "mvn clean package"
    }
    
    stage('Deploy') {
      if (env.BRANCH_NAME == "master") {
        sh "mvn -s ${env.HOME}/usethesource-maven-settings.xml -DskipTests -B deploy"
      }
    }
    
    
    if (currentBuild.previousBuild.result == "FAILURE") { 
      slackSend (color: '#5cb85c', message: "BUILD BACK TO NORMAL: <${env.BUILD_URL}|${env.JOB_NAME} [${env.BUILD_NUMBER}]>")
    }
 
  } catch (e) {
    slackSend (color: '#d9534f', message: "FAILED: <${env.BUILD_URL}|${env.JOB_NAME} [${env.BUILD_NUMBER}]>")
    throw e
  }
}
