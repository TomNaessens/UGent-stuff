Bijzitter::Application.routes.draw do
  root 'welcome#index'

  get 'nonce', to: 'api#nonce'
  post 'letter', to: 'api#letter'

  post 'key', to: 'api#key'
  post 'confirm', to: 'api#confirm'

  post 'check', to: 'api#check'

  get 'clear', to: 'welcome#clear'
  get 'index', to: 'welcome#index'
end
